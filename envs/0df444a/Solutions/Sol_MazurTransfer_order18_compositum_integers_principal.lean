-- Prove2me | solution 1 for MazurTransfer.order18_compositum_integers_principal
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:03:21.627828+00:00
-- url     : https://prove2.me/submissions/075bee86-1e7f-453e-a2d9-b8de390572be

import Mathlib
import Definitions.Def_MazurTransfer_Order18CompositumField

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

















/-- Irreducibility of `S³ - 3S - 10` over `ℚ`. -/
theorem twoDivisionPolynomial_irreducible :
    Irreducible twoDivisionPolynomial := by
  exact MazurTransfer.order18_rational_cubics_irreducible.2




theorem twoDivisionPolynomial_natDegree :
    twoDivisionPolynomial.natDegree = 3 := by
  simp only [twoDivisionPolynomial]
  compute_degree!







/-- The defining relation for `sigma`. -/
theorem sigma_cubic : sigma ^ 3 = 3 * sigma + 10 := by
  have h : AdjoinRoot.mk twoDivisionPolynomial twoDivisionPolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk twoDivisionPolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : sigma ^ 3 - 3 * sigma - 10 = 0 := by
    simpa only [sigma] using h
  linear_combination h'









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



theorem quadraticElement_eq (a b c : Q.K) :
    quadraticElement a b c =
      algebraMap Q.K M a * s ^ 2 + algebraMap Q.K M b * s +
        algebraMap Q.K M c := by
  simp [quadraticElement, s]





/-- Closed formula for the relative norm of a quadratic representative.
This is the determinant of multiplication in the basis `1,s,s²`. -/
theorem norm_quadraticElement (a b c : Q.K) :
    Algebra.norm Q.K (quadraticElement a b c) =
      100 * a ^ 3 - 30 * a ^ 2 * b + 9 * a ^ 2 * c -
        30 * a * b * c + 6 * a * c ^ 2 + 10 * b ^ 3 -
        3 * b ^ 2 * c + c ^ 3 := by
  let pb := AdjoinRoot.powerBasis' relativePolynomial_monic
  rw [quadraticElement_eq, Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_add, map_mul, map_pow]
  rw [(Algebra.leftMulMatrix pb.basis).commutes a,
    (Algebra.leftMulMatrix pb.basis).commutes b,
    (Algebra.leftMulMatrix pb.basis).commutes c]
  have hs : s = pb.gen := rfl
  rw [hs, pb.leftMulMatrix]
  have hmin : pb.minpolyGen = relativePolynomial := by
    dsimp [pb]
    rw [PowerBasis.minpolyGen_eq,
      AdjoinRoot.powerBasis'_gen,
      AdjoinRoot.minpoly_root relativePolynomial_monic.ne_zero,
      relativePolynomial_monic.leadingCoeff, inv_one, C_1, mul_one]
  rw [hmin]
  have hdim : pb.dim = 3 := relativePolynomial_natDegree
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) Q.K :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -relativePolynomial.coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) a *
          companion ^ 2 +
        algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) b *
          companion +
      algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) c) = _
  have hcompanion :
      Matrix.reindexAlgEquiv Q.K Q.K e companion =
        !![0, 0, 10; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, relativePolynomial, coeff_sub,
        coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv Q.K (R := Q.K) e]
  rw [map_add, map_add, map_mul, map_pow, map_mul]
  rw [(Matrix.reindexAlgEquiv Q.K Q.K e).commutes a,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes b,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes c]
  rw [hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring















end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Concrete norm certificates for the `X₁(18)` two-division algebra

This file evaluates the relative norms of the explicit squareclass
representatives used in the two-descent.  The proofs use only the determinant
formula from `XOneEighteenTwoDivisionArithmetic` and the defining cubic
relation for the coefficient generator.  In particular, no field structure on
the relative cubic algebra is used.
-/

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

private theorem tau_pow_four : Q.tau ^ 4 = 3 * Q.tau ^ 2 + Q.tau := by
  calc
    Q.tau ^ 4 = Q.tau * Q.tau ^ 3 := by ring
    _ = Q.tau * (3 * Q.tau + 1) := by rw [Q.tau_cubic]
    _ = 3 * Q.tau ^ 2 + Q.tau := by ring

private theorem tau_pow_five :
    Q.tau ^ 5 = Q.tau ^ 2 + 9 * Q.tau + 3 := by
  calc
    Q.tau ^ 5 = Q.tau * Q.tau ^ 4 := by ring
    _ = Q.tau * (3 * Q.tau ^ 2 + Q.tau) := by rw [tau_pow_four]
    _ = 3 * Q.tau ^ 3 + Q.tau ^ 2 := by ring
    _ = Q.tau ^ 2 + 9 * Q.tau + 3 := by rw [Q.tau_cubic]; ring

private theorem tau_pow_six :
    Q.tau ^ 6 = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by
  calc
    Q.tau ^ 6 = (Q.tau ^ 3) ^ 2 := by ring
    _ = (3 * Q.tau + 1) ^ 2 := by rw [Q.tau_cubic]
    _ = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by ring

/-- The first explicit dyadic generator has relative norm `2`. -/
theorem norm_alpha : Algebra.norm Q.K alpha = 2 := by
  rw [alpha, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring



















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


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/

theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the real cubic coefficient field. -/
def MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic

theorem twoDivisionPolynomial_monic : twoDivisionPolynomial.Monic := by
  simp only [twoDivisionPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the two-division cubic field. -/
def twoDivisionPowerBasis : PowerBasis ℚ F :=
  AdjoinRoot.powerBasis' twoDivisionPolynomial_monic

theorem MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_minpolyGen :
    MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm

theorem twoDivisionPowerBasis_minpolyGen :
    twoDivisionPowerBasis.minpolyGen = twoDivisionPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval sigma twoDivisionPolynomial = 0 := by
    simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
      map_mul, map_ofNat]
    linear_combination sigma_cubic
  exact (minpoly.eq_of_irreducible_of_monic twoDivisionPolynomial_irreducible
    hroot twoDivisionPolynomial_monic).symm

theorem MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim : MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.dim = 3 := by
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!

theorem twoDivisionPowerBasis_dim : twoDivisionPowerBasis.dim = 3 := by
  rw [twoDivisionPowerBasis, AdjoinRoot.powerBasis'_dim]
  exact twoDivisionPolynomial_natDegree

private theorem norm_cubic_derivative
    {L : Type*} [CommRing L] [Algebra ℚ L]
    (pb : PowerBasis ℚ L) (hdim : pb.dim = 3) (d : ℚ)
    (hmin : pb.minpolyGen = X ^ 3 - 3 * X - C d) :
    Algebra.norm ℚ (3 * pb.gen ^ 2 - 3) = 27 * (d ^ 2 - 4) := by
  rw [Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [pb.leftMulMatrix, hmin]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -(X ^ 3 - 3 * X - C d).coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3 *
        companion ^ 2 -
      algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3) = _
  have hcompanion :
      Matrix.reindexAlgEquiv ℚ ℚ e companion =
        !![0, 0, d; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, coeff_sub, coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv ℚ (R := ℚ) e]
  rw [map_sub, map_mul, map_pow]
  rw [(Matrix.reindexAlgEquiv ℚ ℚ e).commutes 3, hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

/-- The exact rational power-basis discriminant of the coefficient cubic. -/
theorem MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_discriminant :
    Algebra.discr ℚ MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_minpolyGen)
  rw [show MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num

/-- The exact rational power-basis discriminant of the two-division cubic. -/
theorem twoDivisionPowerBasis_discriminant :
    Algebra.discr ℚ twoDivisionPowerBasis.basis = -2592 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [twoDivisionPowerBasis.finrank, twoDivisionPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, twoDivisionPowerBasis_minpolyGen]
  simp only [twoDivisionPolynomial, derivative_sub, derivative_pow,
    derivative_X, derivative_mul, derivative_ofNat, mul_one,
    Nat.cast_ofNat, zero_mul, sub_zero]
  rw [show twoDivisionPowerBasis.gen = sigma by rfl]
  have hnorm := norm_cubic_derivative twoDivisionPowerBasis
    twoDivisionPowerBasis_dim 10 (by
      simpa only [twoDivisionPolynomial, Polynomial.C_ofNat] using
        twoDivisionPowerBasis_minpolyGen)
  rw [show twoDivisionPowerBasis.gen = sigma by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]

/-! ## Integral generators and their conductors -/

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1

theorem coefficientPolynomialInt_monic : coefficientPolynomialInt.Monic := by
  simp only [coefficientPolynomialInt]
  monicity <;> norm_num



private theorem coefficientPolynomialInt_aeval_tau :
    Polynomial.aeval Q.tau coefficientPolynomialInt = 0 := by
  simp only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one]
  linear_combination Q.tau_cubic

/-- The coefficient-field generator as an algebraic integer. -/
def coefficientInteger : 𝓞 Q.K :=
  ⟨Q.tau, ⟨coefficientPolynomialInt, coefficientPolynomialInt_monic,
    coefficientPolynomialInt_aeval_tau⟩⟩

theorem coefficientInteger_minpoly :
    minpoly ℤ coefficientInteger = coefficientPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ Q.K
    coefficientInteger.isIntegral
  have hmin := MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ Q.tau = Q.cubicPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ Q.tau = _
  rw [hmin]
  norm_num [coefficientInteger, coefficientPolynomialInt, Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]

/-- The integral polynomial `X³ - 3X - 10`. -/
def twoDivisionPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 10

theorem twoDivisionPolynomialInt_monic : twoDivisionPolynomialInt.Monic := by
  simp only [twoDivisionPolynomialInt]
  monicity <;> norm_num



private theorem twoDivisionPolynomialInt_aeval_sigma :
    Polynomial.aeval sigma twoDivisionPolynomialInt = 0 := by
  simp only [twoDivisionPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination sigma_cubic

/-- The two-division generator as an algebraic integer. -/
def twoDivisionInteger : 𝓞 F :=
  ⟨sigma, ⟨twoDivisionPolynomialInt, twoDivisionPolynomialInt_monic,
    twoDivisionPolynomialInt_aeval_sigma⟩⟩

theorem twoDivisionInteger_minpoly :
    minpoly ℤ twoDivisionInteger = twoDivisionPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ F
    twoDivisionInteger.isIntegral
  have hmin := twoDivisionPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ sigma = twoDivisionPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ sigma = _
  rw [hmin]
  norm_num [twoDivisionInteger, twoDivisionPolynomialInt, twoDivisionPolynomial]

private theorem integer_discriminant_mem_conductor
    {L : Type*} [Field L] [NumberField L]
    (B : PowerBasis ℚ L) (theta : 𝓞 L)
    (hgen : B.gen = (theta : L)) (d : ℤ)
    (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) :
    (d : 𝓞 L) ∈ conductor ℤ theta := by
  have hfield :
      algebraMap (𝓞 L) L (d : 𝓞 L) ∈
        IsLocalization.coeSubmodule L (conductor ℤ theta) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ
      (B := B) (by simpa only [hgen] using theta.isIntegral_coe)
      z.isIntegral_coe
    rw [hdisc] at hz
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_intCast,
      hgen, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ ℚ L] using hz
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule L (conductor ℤ theta)).mp hfield
  have hz' : z = (d : 𝓞 L) := RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The integer `81` lies in the conductor of `ℤ[τ]` in the coefficient
field's full ring of integers. -/
theorem coefficient_discriminant_mem_conductor :
    (81 : 𝓞 Q.K) ∈ conductor ℤ coefficientInteger := by
  apply integer_discriminant_mem_conductor MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    coefficientInteger (by rfl) 81
  exact MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_discriminant

/-- The integer `-2592` lies in the conductor of `ℤ[σ]` in the
two-division field's full ring of integers. -/
theorem twoDivision_discriminant_mem_conductor :
    ((-2592 : ℤ) : 𝓞 F) ∈ conductor ℤ twoDivisionInteger := by
  apply integer_discriminant_mem_conductor twoDivisionPowerBasis
    twoDivisionInteger (by rfl) (-2592)
  exact twoDivisionPowerBasis_discriminant

private theorem not_dvd_exponent_of_mem_conductor_of_isCoprime
    {L : Type*} [Field L] [NumberField L] (theta : 𝓞 L)
    {p : ℕ} [Fact p.Prime] (d : ℤ)
    (hd : (d : 𝓞 L) ∈ conductor ℤ theta)
    (hcop : IsCoprime d (p : ℤ)) :
    ¬ p ∣ RingOfIntegers.exponent theta := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {d} ≤
      Ideal.comap (algebraMap ℤ (𝓞 L)) (conductor ℤ theta) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    change algebraMap ℤ (𝓞 L) d ∈ conductor ℤ theta at hd
    exact hd
  exact ((Ideal.isCoprime_span_singleton_iff d (p : ℤ)).mpr hcop).codisjoint.mono_left hspan

/-! ## Exact finite-field irreducibility certificates -/

def coefficientPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 1

def twoDivisionPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 10

theorem coefficientPolynomialInt_map_zmod (p : ℕ) :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod p)) =
      coefficientPolynomialMod p := by
  norm_num [coefficientPolynomialInt, coefficientPolynomialMod]

theorem twoDivisionPolynomialInt_map_zmod (p : ℕ) :
    twoDivisionPolynomialInt.map (Int.castRingHom (ZMod p)) =
      twoDivisionPolynomialMod p := by
  norm_num [twoDivisionPolynomialInt, twoDivisionPolynomialMod]

private theorem coefficientPolynomialMod_irreducible_of_no_root
    {p : ℕ} [Fact p.Prime]
    (hroot : ∀ z : ZMod p, ¬ Polynomial.IsRoot (coefficientPolynomialMod p) z) :
    Irreducible (coefficientPolynomialMod p) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ hroot
  have hdegree : (coefficientPolynomialMod p).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  rw [hdegree]
  norm_num

private theorem twoDivisionPolynomialMod_irreducible_of_no_root
    {p : ℕ} [Fact p.Prime]
    (hroot : ∀ z : ZMod p, ¬ Polynomial.IsRoot (twoDivisionPolynomialMod p) z) :
    Irreducible (twoDivisionPolynomialMod p) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ hroot
  have hdegree : (twoDivisionPolynomialMod p).natDegree = 3 := by
    simp only [twoDivisionPolynomialMod]
    compute_degree!
  rw [hdegree]
  norm_num

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_five_irreducible :
    Irreducible (coefficientPolynomialMod 5) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_seven_irreducible :
    Irreducible (coefficientPolynomialMod 7) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_eleven_irreducible :
    Irreducible (coefficientPolynomialMod 11) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_thirteen_irreducible :
    Irreducible (coefficientPolynomialMod 13) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

theorem twoDivisionPolynomialMod_seventeen_irreducible :
    Irreducible (twoDivisionPolynomialMod 17) := by
  apply twoDivisionPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [twoDivisionPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

theorem twoDivisionPolynomialMod_nineteen_irreducible :
    Irreducible (twoDivisionPolynomialMod 19) := by
  apply twoDivisionPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [twoDivisionPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_twentythree_irreducible :
    Irreducible (coefficientPolynomialMod 23) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_twentynine_irreducible :
    Irreducible (coefficientPolynomialMod 29) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

local instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_thirtyone_irreducible :
    Irreducible (coefficientPolynomialMod 31) := by
  apply coefficientPolynomialMod_irreducible_of_no_root
  intro z
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  fin_cases z <;> decide

/-! ## Kummer--Dedekind and inertia in the compositum -/

private theorem inertiaDeg_eq_natDegree_of_irreducible_mod
    {L : Type*} [Field L] [NumberField L] (theta : 𝓞 L)
    {p : ℕ} [Fact p.Prime]
    (hexponent : ¬ p ∣ RingOfIntegers.exponent theta)
    (hirr : Irreducible
      ((minpoly ℤ theta).map (Int.castRingHom (ZMod p))))
    (P : Ideal (𝓞 L))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)) :
    P.inertiaDeg ℤ =
      ((minpoly ℤ theta).map (Int.castRingHom (ZMod p))).natDegree := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexponent
  have hfactor := (e ⟨P, hP⟩).2
  have hdegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      hexponent hfactor
  simp only [Subtype.coe_eta] at hdegree
  change (e ⟨P, hP⟩ : Polynomial (ZMod p)) ∈
      (normalizedFactors
        ((minpoly ℤ theta).map (Int.castRingHom (ZMod p)))).toFinset at hfactor
  rw [normalizedFactors_irreducible hirr,
    (minpoly.monic theta.isIntegral).map
      (Int.castRingHom (ZMod p)) |>.normalize_eq_self] at hfactor
  simp only [Multiset.toFinset_singleton, Finset.mem_singleton] at hfactor
  rw [hfactor] at hdegree
  have heq := e.symm_apply_apply ⟨P, hP⟩
  have hideal :
      ((e.symm (e ⟨P, hP⟩)).1 : Ideal (𝓞 L)) = P :=
    congrArg Subtype.val heq
  rw [hideal] at hdegree
  exact hdegree

private theorem coefficient_inertiaDeg_eq_three
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (81 : ℤ) (p : ℤ))
    (hirr : Irreducible (coefficientPolynomialMod p))
    (P : Ideal (𝓞 Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 Q.K)) :
    P.inertiaDeg ℤ = 3 := by
  have hexponent : ¬ p ∣ RingOfIntegers.exponent coefficientInteger :=
    not_dvd_exponent_of_mem_conductor_of_isCoprime coefficientInteger 81
      coefficient_discriminant_mem_conductor hcop
  have hirr' : Irreducible
      ((minpoly ℤ coefficientInteger).map (Int.castRingHom (ZMod p))) := by
    rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod]
    exact hirr
  have hdegree := inertiaDeg_eq_natDegree_of_irreducible_mod
    coefficientInteger hexponent hirr' P hP
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (coefficientPolynomialMod p).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

private theorem twoDivision_inertiaDeg_eq_three
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime ((-2592 : ℤ)) (p : ℤ))
    (hirr : Irreducible (twoDivisionPolynomialMod p))
    (P : Ideal (𝓞 F))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)) :
    P.inertiaDeg ℤ = 3 := by
  have hexponent : ¬ p ∣ RingOfIntegers.exponent twoDivisionInteger :=
    not_dvd_exponent_of_mem_conductor_of_isCoprime twoDivisionInteger (-2592)
      twoDivision_discriminant_mem_conductor hcop
  have hirr' : Irreducible
      ((minpoly ℤ twoDivisionInteger).map (Int.castRingHom (ZMod p))) := by
    rw [twoDivisionInteger_minpoly, twoDivisionPolynomialInt_map_zmod]
    exact hirr
  have hdegree := inertiaDeg_eq_natDegree_of_irreducible_mod
    twoDivisionInteger hexponent hirr' P hP
  rw [twoDivisionInteger_minpoly, twoDivisionPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (twoDivisionPolynomialMod p).natDegree = 3 := by
    simp only [twoDivisionPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

private theorem s_isRoot_twoDivisionPolynomial :
    Polynomial.aeval s twoDivisionPolynomial = 0 := by
  simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination s_cubic

/-- The canonical embedding of the rational two-division cubic field into
the degree-nine compositum. -/
def twoDivisionEmbedding : F →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom twoDivisionPolynomial (Algebra.ofId ℚ M) s
    s_isRoot_twoDivisionPolynomial

private theorem compositum_inertiaDeg_ge_three_via_coefficient
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (81 : ℤ) (p : ℤ))
    (hirr : Irreducible (coefficientPolynomialMod p))
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  let QP : Ideal (𝓞 Q.K) := P.under (𝓞 Q.K)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 Q.K) :=
    ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three hcop hirr QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ) ⟨P.inertiaDeg (𝓞 Q.K), htower⟩

private theorem compositum_inertiaDeg_ge_three_via_twoDivision
    {p : ℕ} [Fact p.Prime]
    (hcop : IsCoprime (-2592 : ℤ) (p : ℤ))
    (hirr : Irreducible (twoDivisionPolynomialMod p))
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : Algebra F M := twoDivisionEmbedding.toRingHom.toAlgebra
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom twoDivisionEmbedding
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  let QP : Ideal (𝓞 F) := P.under (𝓞 F)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F) :=
    ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    twoDivision_inertiaDeg_eq_three hcop hirr QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ) ⟨P.inertiaDeg (𝓞 F), htower⟩

/-- Every prime of the compositum over a rational prime in `[5,31]` has
inertia degree at least three. -/
theorem compositum_inertiaDeg_ge_three
    (p : ℕ) (hpIcc : p ∈ Finset.Icc 5 31) (hp : p.Prime)
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    3 ≤ P.inertiaDeg ℤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpLower : 5 ≤ p := Finset.mem_Icc.mp hpIcc |>.1
  have hpUpper : p ≤ 31 := Finset.mem_Icc.mp hpIcc |>.2
  interval_cases p <;> norm_num at hp
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_five_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_seven_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_eleven_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_thirteen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_twoDivision
      (by norm_num) twoDivisionPolynomialMod_seventeen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_twoDivision
      (by norm_num) twoDivisionPolynomialMod_nineteen_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_twentythree_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_twentynine_irreducible P hP
  · exact compositum_inertiaDeg_ge_three_via_coefficient
      (by norm_num) coefficientPolynomialMod_thirtyone_irreducible P hP

/-- Consequently, no prime ideal over a rational prime in `[5,31]` can
have absolute norm at most `31`. -/
theorem thirtyone_lt_absNorm_of_mem_primesOver
    (p : ℕ) (hpIcc : p ∈ Finset.Icc 5 31) (hp : p.Prime)
    (P : Ideal (𝓞 M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 M)) :
    31 < P.absNorm := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg p P]
  have hdegree := compositum_inertiaDeg_ge_three p hpIcc hp P hP
  have hpge : 5 ≤ p := Finset.mem_Icc.mp hpIcc |>.1
  calc
    31 < p ^ 3 := lt_of_lt_of_le (by norm_num : 31 < 5 ^ 3)
      (Nat.pow_le_pow_left hpge 3)
    _ ≤ p ^ P.inertiaDeg ℤ := pow_le_pow_right' (by omega) hdegree

end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

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


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallDiscriminant. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A small-discriminant model of the `X₁(18)` two-division compositum

Starting from the primitive element `u = t - s`, this file constructs a
second generator with a substantially smaller defining polynomial.  Both
changes of generator are checked by explicit bounded polynomial identities.

The resulting power basis is a power basis over `ℚ`.  No assertion is made
that its integral span is the full ring of integers.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive

/-- The normalized degree-nine polynomial. -/
def normalizedPolynomial : Polynomial ℚ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomial_monic : normalizedPolynomial.Monic := by
  simp only [normalizedPolynomial]
  monicity <;> norm_num

theorem normalizedPolynomial_natDegree :
    normalizedPolynomial.natDegree = 9 := by
  simp only [normalizedPolynomial]
  compute_degree!

private def discrP₀ : Polynomial ℚ := normalizedPolynomial

private def discrP₁ : Polynomial ℚ :=
  9 * X ^ 8 - 24 * X ^ 7 + 42 * X ^ 5 - 15 * X ^ 4 -
    36 * X ^ 3 + 9 * X ^ 2 + 12 * X

private def discrP₂ : Polynomial ℚ :=
  8 * X ^ 7 - 21 * X ^ 6 - 2 * X ^ 5 + 50 * X ^ 4 -
    6 * X ^ 3 - 45 * X ^ 2 - 4 * X + 9

private def discrP₃ : Polynomial ℚ :=
  3 * X ^ 6 - 34 * X ^ 5 - 14 * X ^ 4 + 34 * X ^ 3 +
    27 * X ^ 2 + 4 * X + 1

private def discrP₄ : Polynomial ℚ :=
  58 * X ^ 5 + 20 * X ^ 4 - 61 * X ^ 3 - 48 * X ^ 2 - 7 * X - 1

private def discrP₅ : Polynomial ℚ :=
  231 * X ^ 4 - 68 * X ^ 3 - 305 * X ^ 2 - 33 * X + 74

private def discrP₆ : Polynomial ℚ :=
  1681 * X ^ 3 + 586 * X ^ 2 - 1287 * X - 817

private def discrP₇ : Polynomial ℚ :=
  337 * X ^ 2 + 152 * X - 8

private def discrP₈ : Polynomial ℚ := 47 * X + 33

private def discrP₉ : Polynomial ℚ := 1

private theorem discrP₀_degree : discrP₀.natDegree = 9 := by
  simpa only [discrP₀] using normalizedPolynomial_natDegree

private theorem discrP₁_degree : discrP₁.natDegree = 8 := by
  simp only [discrP₁]
  compute_degree!

private theorem discrP₂_degree : discrP₂.natDegree = 7 := by
  simp only [discrP₂]
  compute_degree!

private theorem discrP₃_degree : discrP₃.natDegree = 6 := by
  simp only [discrP₃]
  compute_degree!

private theorem discrP₄_degree : discrP₄.natDegree = 5 := by
  simp only [discrP₄]
  compute_degree!

private theorem discrP₅_degree : discrP₅.natDegree = 4 := by
  simp only [discrP₅]
  compute_degree!

private theorem discrP₆_degree : discrP₆.natDegree = 3 := by
  simp only [discrP₆]
  compute_degree!

private theorem discrP₇_degree : discrP₇.natDegree = 2 := by
  simp only [discrP₇]
  compute_degree!

private theorem discrP₈_degree : discrP₈.natDegree = 1 := by
  simp only [discrP₈]
  compute_degree!

private theorem discrP₉_degree : discrP₉.natDegree = 0 := by
  simp only [discrP₉, natDegree_one]

private theorem discrP₁_leadingCoeff : discrP₁.leadingCoeff = 9 := by
  rw [← coeff_natDegree, discrP₁_degree]
  norm_num [discrP₁]
  simp only [coeff_X]
  norm_num

private theorem discrP₂_leadingCoeff : discrP₂.leadingCoeff = 8 := by
  rw [← coeff_natDegree, discrP₂_degree]
  norm_num [discrP₂]
  simp only [coeff_X]
  norm_num

private theorem discrP₃_leadingCoeff : discrP₃.leadingCoeff = 3 := by
  rw [← coeff_natDegree, discrP₃_degree]
  norm_num [discrP₃]
  simp only [coeff_X, coeff_one]
  norm_num

private theorem discrP₄_leadingCoeff : discrP₄.leadingCoeff = 58 := by
  rw [← coeff_natDegree, discrP₄_degree]
  norm_num [discrP₄]
  simp only [coeff_X, coeff_one]
  norm_num

private theorem discrP₅_leadingCoeff : discrP₅.leadingCoeff = 231 := by
  rw [← coeff_natDegree, discrP₅_degree]
  norm_num [discrP₅]
  simp only [coeff_X]
  norm_num

private theorem discrP₆_leadingCoeff : discrP₆.leadingCoeff = 1681 := by
  rw [← coeff_natDegree, discrP₆_degree]
  norm_num [discrP₆]
  simp only [coeff_X]
  norm_num

private theorem discrP₇_leadingCoeff : discrP₇.leadingCoeff = 337 := by
  rw [← coeff_natDegree, discrP₇_degree]
  norm_num [discrP₇]
  simp only [coeff_X]
  norm_num

private theorem discrP₈_leadingCoeff : discrP₈.leadingCoeff = 47 := by
  rw [← coeff_natDegree, discrP₈_degree]
  norm_num [discrP₈]

private theorem resultant_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) :
    f.resultant g =
      g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := by
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

private theorem resultant_step_scaled {f g r q : Polynomial ℚ}
    {c d : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : C d * f = C c * r + g * q) (hd : d ≠ 0) :
    f.resultant g =
      g.leadingCoeff ^ 2 * (c / d) ^ (k + 1) * g.resultant r := by
  have hscaledDegree : (C d * f).natDegree = k + 2 := by
    rw [natDegree_C_mul hd, hf]
  have hstep := resultant_step hscaledDegree hg hr hq hrel
  have hscaleResultant :
      (C d * f).resultant g = d ^ (k + 1) * f.resultant g := by
    change resultant (C d * f) g (C d * f).natDegree g.natDegree = _
    rw [natDegree_C_mul hd, hf, hg, resultant_C_mul_left]
  rw [hscaleResultant] at hstep
  apply mul_left_cancel₀ (pow_ne_zero (k + 1) hd)
  calc
    d ^ (k + 1) * f.resultant g =
        g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := hstep
    _ = d ^ (k + 1) *
        (g.leadingCoeff ^ 2 * (c / d) ^ (k + 1) *
          g.resultant r) := by
      rw [div_pow]
      field_simp [pow_ne_zero (k + 1) hd]

private theorem discrP₀_resultant_discrP₁ :
    discrP₀.resultant discrP₁ =
      discrP₁.leadingCoeff ^ 2 * ((-3 : ℚ) / 27) ^ 8 *
        discrP₁.resultant discrP₂ := by
  apply resultant_step_scaled
    (q := 3 * X - 1) (c := -3) (d := 27) (k := 7)
  · simpa using discrP₀_degree
  · simpa using discrP₁_degree
  · simpa using discrP₂_degree
  · compute_degree!
  · simp only [discrP₀, discrP₁, discrP₂,
      normalizedPolynomial]
    simp only [map_neg, Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₁_resultant_discrP₂ :
    discrP₁.resultant discrP₂ =
      discrP₂.leadingCoeff ^ 2 * ((27 : ℚ) / 64) ^ 7 *
        discrP₂.resultant discrP₃ := by
  apply resultant_step_scaled
    (q := 72 * X - 3) (c := 27) (d := 64) (k := 6)
  · simpa using discrP₁_degree
  · simpa using discrP₂_degree
  · simpa using discrP₃_degree
  · compute_degree!
  · simp only [discrP₁, discrP₂, discrP₃]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₂_resultant_discrP₃ :
    discrP₂.resultant discrP₃ =
      discrP₃.leadingCoeff ^ 2 * ((128 : ℚ) / 9) ^ 6 *
        discrP₃.resultant discrP₄ := by
  apply resultant_step_scaled
    (q := 24 * X + 209) (c := 128) (d := 9) (k := 5)
  · simpa using discrP₂_degree
  · simpa using discrP₃_degree
  · simpa using discrP₄_degree
  · compute_degree!
  · simp only [discrP₂, discrP₃, discrP₄]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₃_resultant_discrP₄ :
    discrP₃.resultant discrP₄ =
      discrP₄.leadingCoeff ^ 2 * ((9 : ℚ) / 1682) ^ 5 *
        discrP₄.resultant discrP₅ := by
  apply resultant_step_scaled
    (q := 87 * X - 1016) (c := 9) (d := 1682) (k := 4)
  · simpa using discrP₃_degree
  · simpa using discrP₄_degree
  · simpa using discrP₅_degree
  · compute_degree!
  · simp only [discrP₃, discrP₄, discrP₅]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₄_resultant_discrP₅ :
    discrP₄.resultant discrP₅ =
      discrP₅.leadingCoeff ^ 2 * ((841 : ℚ) / 53361) ^ 4 *
        discrP₅.resultant discrP₆ := by
  apply resultant_step_scaled
    (q := 13398 * X + 8564) (c := 841) (d := 53361) (k := 3)
  · simpa using discrP₄_degree
  · simpa using discrP₅_degree
  · simpa using discrP₆_degree
  · compute_degree!
  · simp only [discrP₄, discrP₅, discrP₆]
    simp only [Polynomial.C_ofNat]
    ring
  · norm_num

private theorem discrP₅_resultant_discrP₆ :
    discrP₅.resultant discrP₆ =
      discrP₆.leadingCoeff ^ 2 * ((-640332 : ℚ) / 2825761) ^ 3 *
        discrP₆.resultant discrP₇ := by
  apply resultant_step_scaled
    (q := 388311 * X - 249674) (c := -640332) (d := 2825761)
      (k := 2)
  · simpa using discrP₅_degree
  · simpa using discrP₆_degree
  · simpa using discrP₇_degree
  · compute_degree!
  · simp only [discrP₅, discrP₆, discrP₇]
    simp only [map_neg, Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem discrP₆_resultant_discrP₇ :
    discrP₆.resultant discrP₇ =
      discrP₇.leadingCoeff ^ 2 * ((-2825761 : ℚ) / 113569) ^ 2 *
        discrP₇.resultant discrP₈ := by
  apply resultant_step_scaled
    (q := 566497 * X - 58030) (c := -2825761) (d := 113569)
      (k := 1)
  · simpa using discrP₆_degree
  · simpa using discrP₇_degree
  · simpa using discrP₈_degree
  · compute_degree!
  · simp only [discrP₆, discrP₇, discrP₈]
    simp only [map_neg, Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem discrP₇_resultant_discrP₈ :
    discrP₇.resultant discrP₈ =
      discrP₈.leadingCoeff ^ 2 * ((113569 : ℚ) / 2209) ^ 1 *
        discrP₈.resultant discrP₉ := by
  apply resultant_step_scaled
    (q := 15839 * X - 3977) (c := 113569) (d := 2209) (k := 0)
  · simpa using discrP₇_degree
  · simpa using discrP₈_degree
  · simpa using discrP₉_degree
  · compute_degree!
  · simp only [discrP₇, discrP₈, discrP₉]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num

private theorem normalizedPolynomial_derivative :
    normalizedPolynomial.derivative = discrP₁ := by
  simp only [normalizedPolynomial, discrP₁, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    Nat.cast_ofNat, mul_one, zero_mul]
  simp only [Polynomial.C_ofNat]
  norm_num
  ring

private theorem discrP₀_resultant_discrP₁_exact :
    discrP₀.resultant discrP₁ = -272097792 := by
  rw [discrP₀_resultant_discrP₁, discrP₁_resultant_discrP₂,
    discrP₂_resultant_discrP₃, discrP₃_resultant_discrP₄,
    discrP₄_resultant_discrP₅, discrP₅_resultant_discrP₆,
    discrP₆_resultant_discrP₇, discrP₇_resultant_discrP₈]
  rw [discrP₁_leadingCoeff, discrP₂_leadingCoeff,
    discrP₃_leadingCoeff, discrP₄_leadingCoeff,
    discrP₅_leadingCoeff, discrP₆_leadingCoeff,
    discrP₇_leadingCoeff, discrP₈_leadingCoeff]
  norm_num [discrP₉, resultant_C_right, discrP₈_degree]

/-- The exact discriminant of the normalized rational power basis.  Its
factorization is `-2⁹·3¹²`. -/
theorem normalizedPolynomial_discr :
    normalizedPolynomial.discr = -272097792 := by
  have hdegree : 0 < normalizedPolynomial.degree :=
    natDegree_pos_iff_degree_pos.mp
      (by rw [normalizedPolynomial_natDegree]; norm_num)
  have hres := Polynomial.resultant_deriv
    (f := normalizedPolynomial) hdegree
  rw [normalizedPolynomial_natDegree,
    normalizedPolynomial_monic.leadingCoeff] at hres
  norm_num at hres
  rw [← hres, normalizedPolynomial_derivative]
  have hexact := discrP₀_resultant_discrP₁_exact
  change resultant discrP₀ discrP₁ discrP₀.natDegree
    discrP₁.natDegree = -272097792 at hexact
  rw [discrP₀_degree, discrP₁_degree] at hexact
  simpa only [discrP₀] using hexact



private def forwardNumerator : Polynomial ℚ :=
  X ^ 8 - 12 * X ^ 7 - 15 * X ^ 6 + 261 * X ^ 5 -
    243 * X ^ 4 - 1377 * X ^ 3 + 1377 * X ^ 2 - 3402 * X + 2673

/-- The forward change of generator, from `u` to the normalized generator. -/
def forwardPolynomial : Polynomial ℚ :=
  C (1 / 5346) * forwardNumerator

/-- The inverse change of generator. -/
def inversePolynomial : Polynomial ℚ :=
  -X ^ 6 + 4 * X ^ 5 - 4 * X ^ 4 - 4 * X ^ 3 +
    8 * X ^ 2 - 4

/-- The normalized generator in the degree-nine compositum. -/
def normalizedElement : M :=
  Polynomial.aeval primitiveElement forwardPolynomial



private def primitiveCertificateLeft : Polynomial ℚ :=
  X ^ 18 - 15 * X ^ 17 + 99 * X ^ 16 - 370 * X ^ 15 +
    822 * X ^ 14 - 951 * X ^ 13 - 38 * X ^ 12 + 1860 * X ^ 11 -
    2490 * X ^ 10 + 583 * X ^ 9 + 1911 * X ^ 8 - 2079 * X ^ 7 +
    325 * X ^ 6 + 729 * X ^ 5 - 417 * X ^ 4 - 18 * X ^ 3 +
    48 * X ^ 2 + 1

private def primitiveCertificateRight : Polynomial ℚ :=
  X ^ 27 - 18 * X ^ 26 + 144 * X ^ 25 - 648 * X ^ 24 +
    1632 * X ^ 23 - 1344 * X ^ 22 - 5118 * X ^ 21 +
    18660 * X ^ 20 - 19032 * X ^ 19 - 28109 * X ^ 18 +
    100284 * X ^ 17 - 69132 * X ^ 16 - 139269 * X ^ 15 +
    291906 * X ^ 14 - 44040 * X ^ 13 - 416277 * X ^ 12 +
    389016 * X ^ 11 + 236328 * X ^ 10 - 567261 * X ^ 9 +
    87198 * X ^ 8 + 428580 * X ^ 7 - 241218 * X ^ 6 -
    178008 * X ^ 5 + 178008 * X ^ 4 + 33333 * X ^ 3 -
    66666 * X ^ 2 + 11573

private def inverseCertificate : Polynomial ℚ :=
  X ^ 39 - 29 * X ^ 38 + 393 * X ^ 37 - 3276 * X ^ 36 +
    18538 * X ^ 35 - 73551 * X ^ 34 + 199718 * X ^ 33 -
    316038 * X ^ 32 - 9396 * X ^ 31 + 1492518 * X ^ 30 -
    3811884 * X ^ 29 + 3342246 * X ^ 28 + 5571187 * X ^ 27 -
    20469077 * X ^ 26 + 20282946 * X ^ 25 + 18324779 * X ^ 24 -
    72486147 * X ^ 23 + 59978295 * X ^ 22 + 62314925 * X ^ 21 -
    176704300 * X ^ 20 + 91592559 * X ^ 19 + 166289854 * X ^ 18 -
    278593602 * X ^ 17 + 39708081 * X ^ 16 + 278712309 * X ^ 15 -
    250996431 * X ^ 14 - 79815546 * X ^ 13 + 259471817 * X ^ 12 -
    96550462 * X ^ 11 - 117315852 * X ^ 10 + 114862674 * X ^ 9 +
    6336218 * X ^ 8 - 51676242 * X ^ 7 + 16470556 * X ^ 6 +
    9620757 * X ^ 5 - 6095061 * X ^ 4 - 229751 * X ^ 3 +
    551578 * X ^ 2 + 5346 * X + 2327

private abbrev NormalizedAdjoinRoot := AdjoinRoot normalizedPolynomial

private abbrev normalizedRoot : NormalizedAdjoinRoot :=
  AdjoinRoot.root normalizedPolynomial

private theorem normalizedRoot_root :
    Polynomial.aeval normalizedRoot normalizedPolynomial = 0 := by
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root normalizedPolynomial

private theorem primitive_change_identity :
    primitivePolynomial.comp inversePolynomial =
      -primitiveCertificateLeft * primitiveCertificateRight *
        normalizedPolynomial := by
  simp only [primitivePolynomial, inversePolynomial, primitiveCertificateLeft,
    primitiveCertificateRight, normalizedPolynomial, add_comp, sub_comp,
    mul_comp, pow_comp, X_comp, ofNat_comp]
  ring

private theorem inverse_change_identity :
    forwardPolynomial.comp inversePolynomial - X =
      C (1 / 5346) * inverseCertificate * normalizedPolynomial := by
  have hnumerator :
      forwardNumerator.comp inversePolynomial - 5346 * X =
        inverseCertificate * normalizedPolynomial := by
    simp only [forwardNumerator, inversePolynomial, inverseCertificate,
      normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp, X_comp,
      ofNat_comp]
    ring
  have hc : C (1 / 5346 : ℚ) * (5346 : Polynomial ℚ) = 1 := by
    change C (1 / 5346 : ℚ) * C (5346 : ℚ) = C (1 : ℚ)
    rw [← C_mul]
    norm_num
  have hscaled := congrArg
    (fun p : Polynomial ℚ ↦ C (1 / 5346) * p) hnumerator
  rw [mul_sub, ← mul_assoc, hc, one_mul] at hscaled
  simpa only [forwardPolynomial, mul_comp, C_comp, mul_assoc] using hscaled

private theorem primitive_of_inverse_root :
    Polynomial.aeval (Polynomial.aeval normalizedRoot inversePolynomial)
      primitivePolynomial = 0 := by
  rw [← Polynomial.aeval_comp, primitive_change_identity]
  simp only [map_mul, normalizedRoot_root, mul_zero]

private theorem forward_of_inverse_root :
    Polynomial.aeval
      (Polynomial.aeval normalizedRoot inversePolynomial) forwardPolynomial =
        normalizedRoot := by
  have h := congrArg (Polynomial.aeval normalizedRoot) inverse_change_identity
  simp only [map_sub, Polynomial.aeval_comp, aeval_X, map_mul, aeval_C,
    normalizedRoot_root, mul_zero] at h
  exact sub_eq_zero.mp h

/-- The explicit old-to-normalized change of presentation. -/
def primitiveToNormalizedHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AdjoinRoot.liftAlgHom primitivePolynomial
    (Algebra.ofId ℚ (AdjoinRoot normalizedPolynomial))
    (Polynomial.aeval normalizedRoot inversePolynomial) (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitive_of_inverse_root)

@[simp]
theorem primitiveToNormalizedHom_root :
    primitiveToNormalizedHom (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitiveToNormalizedHom_forward :
    primitiveToNormalizedHom
        (Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
          forwardPolynomial) = normalizedRoot := by
  rw [← Polynomial.aeval_algHom_apply, primitiveToNormalizedHom_root]
  exact forward_of_inverse_root

private instance normalizedAdjoinRootNontrivial :
    Nontrivial (AdjoinRoot normalizedPolynomial) := by
  apply AdjoinRoot.nontrivial
  rw [degree_eq_natDegree normalizedPolynomial_monic.ne_zero,
    normalizedPolynomial_natDegree]
  norm_num

private theorem primitiveToNormalizedHom_injective :
    Function.Injective primitiveToNormalizedHom := by
  exact RingHom.injective primitiveToNormalizedHom.toRingHom

private theorem primitiveToNormalizedHom_surjective :
    Function.Surjective primitiveToNormalizedHom := by
  apply (AlgHom.range_eq_top primitiveToNormalizedHom).mp
  rw [← top_le_iff, ← AdjoinRoot.adjoinRoot_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitiveToNormalizedHom).2
    ⟨Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
      forwardPolynomial, primitiveToNormalizedHom_forward⟩

/-- The two explicit changes of generator give an equivalence between the
old and normalized quotient presentations. -/
def primitiveToNormalizedEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AlgEquiv.ofBijective primitiveToNormalizedHom
    ⟨primitiveToNormalizedHom_injective,
      primitiveToNormalizedHom_surjective⟩

@[simp]
theorem primitiveToNormalizedEquiv_root :
    primitiveToNormalizedEquiv (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact primitiveToNormalizedHom_root

private theorem primitiveToNormalizedEquiv_symm_root :
    primitiveToNormalizedEquiv.symm normalizedRoot =
      Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
        forwardPolynomial := by
  apply primitiveToNormalizedEquiv.injective
  rw [primitiveToNormalizedEquiv.apply_symm_apply]
  exact primitiveToNormalizedHom_forward.symm

private def primitivePresentationHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom primitivePolynomial (Algebra.ofId ℚ M)
    primitiveElement (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitiveElement_root)

@[simp]
private theorem primitivePresentationHom_root :
    primitivePresentationHom (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitivePresentationHom_injective :
    Function.Injective primitivePresentationHom := by
  exact RingHom.injective primitivePresentationHom.toRingHom

private theorem primitivePresentationHom_surjective :
    Function.Surjective primitivePresentationHom := by
  apply (AlgHom.range_eq_top primitivePresentationHom).mp
  rw [← top_le_iff, ← primitiveElement_adjoin_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitivePresentationHom).2
    ⟨AdjoinRoot.root primitivePolynomial, primitivePresentationHom_root⟩

private def primitivePresentationEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] M :=
  AlgEquiv.ofBijective primitivePresentationHom
    ⟨primitivePresentationHom_injective,
      primitivePresentationHom_surjective⟩

@[simp]
private theorem primitivePresentationEquiv_root :
    primitivePresentationEquiv (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact primitivePresentationHom_root

/-- The normalized polynomial quotient is the original degree-nine
two-division compositum. -/
def normalizedAdjoinRootEquiv :
    AdjoinRoot normalizedPolynomial ≃ₐ[ℚ] M :=
  primitiveToNormalizedEquiv.symm.trans primitivePresentationEquiv

@[simp]
theorem normalizedAdjoinRootEquiv_root :
    normalizedAdjoinRootEquiv normalizedRoot = normalizedElement := by
  rw [normalizedAdjoinRootEquiv, AlgEquiv.trans_apply,
    primitiveToNormalizedEquiv_symm_root]
  rw [← Polynomial.aeval_algHom_apply, primitivePresentationEquiv_root]
  rfl

/-- The normalized generator satisfies the advertised small polynomial. -/
theorem normalizedElement_root :
    Polynomial.aeval normalizedElement normalizedPolynomial = 0 := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply, normalizedRoot_root, map_zero]

/-- The inverse polynomial recovers `u = t - s` from the normalized
generator. -/
theorem normalizedElement_reconstruction :
    Polynomial.aeval normalizedElement inversePolynomial =
      primitiveElement := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply]
  change primitivePresentationEquiv
      (primitiveToNormalizedEquiv.symm
        (Polynomial.aeval normalizedRoot inversePolynomial)) =
    primitiveElement
  rw [← primitiveToNormalizedEquiv_root,
    primitiveToNormalizedEquiv.symm_apply_apply,
    primitivePresentationEquiv_root]

theorem primitiveElement_mem_normalized_adjoin :
    primitiveElement ∈
      Algebra.adjoin ℚ ({normalizedElement} : Set M) := by
  rw [← normalizedElement_reconstruction]
  exact Polynomial.aeval_mem_adjoin_singleton ℚ normalizedElement

/-- The normalized element still generates the full compositum over `ℚ`. -/
theorem normalizedElement_adjoin_eq_top :
    Algebra.adjoin ℚ ({normalizedElement} : Set M) = ⊤ := by
  apply le_antisymm le_top
  rw [← primitiveElement_adjoin_eq_top]
  exact Algebra.adjoin_le
    (Set.singleton_subset_iff.mpr primitiveElement_mem_normalized_adjoin)

theorem normalizedElement_isIntegral :
    IsIntegral ℚ normalizedElement :=
  ⟨normalizedPolynomial, normalizedPolynomial_monic,
    normalizedElement_root⟩

/-- The rational power basis generated by the normalized element.  This is
not asserted to be an integral basis over `ℤ`. -/
def normalizedPowerBasis : PowerBasis ℚ M :=
  PowerBasis.ofAdjoinEqTop normalizedElement_isIntegral
    normalizedElement_adjoin_eq_top

@[simp]
theorem normalizedPowerBasis_gen :
    normalizedPowerBasis.gen = normalizedElement := by
  rw [normalizedPowerBasis, PowerBasis.ofAdjoinEqTop_gen]

theorem normalizedElement_minpoly_natDegree :
    (minpoly ℚ normalizedElement).natDegree = 9 := by
  calc
    (minpoly ℚ normalizedElement).natDegree = normalizedPowerBasis.dim := by
      simpa only [normalizedPowerBasis_gen] using
        normalizedPowerBasis.natDegree_minpoly
    _ = Module.finrank ℚ M := normalizedPowerBasis.finrank.symm
    _ = 9 := finrank_M_over_rat

/-- The normalized polynomial is exactly the minimal polynomial. -/
theorem normalizedElement_minpoly :
    minpoly ℚ normalizedElement = normalizedPolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic normalizedElement_isIntegral)
    normalizedPolynomial_monic
    (minpoly.dvd ℚ normalizedElement normalizedElement_root)
    (by rw [normalizedPolynomial_natDegree,
      normalizedElement_minpoly_natDegree])).symm

theorem normalizedPolynomial_irreducible :
    Irreducible normalizedPolynomial := by
  rw [← normalizedElement_minpoly]
  exact minpoly.irreducible normalizedElement_isIntegral

instance normalizedPolynomial_irreducibleFact :
    Fact (Irreducible normalizedPolynomial) :=
  ⟨normalizedPolynomial_irreducible⟩

end

end MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The integral normalized model of the `X₁(18)` two-division compositum

This file records the integer polynomial underlying the normalized rational
power basis and lifts its generator to the full ring of integers.  It makes
no claim that the resulting order is the maximal order.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

/-- The monic integer polynomial underlying `normalizedPolynomial`. -/
def normalizedPolynomialInt : Polynomial ℤ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomialInt_monic : normalizedPolynomialInt.Monic := by
  simp only [normalizedPolynomialInt]
  monicity <;> norm_num





theorem normalizedPolynomialInt_aeval :
    Polynomial.aeval normalizedElement normalizedPolynomialInt = 0 := by
  simpa only [normalizedPolynomialInt, normalizedPolynomial, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one, aeval_X] using
      normalizedElement_root

/-- The normalized generator is an algebraic integer. -/
theorem normalizedElement_isIntegral_int :
    IsIntegral ℤ normalizedElement :=
  ⟨normalizedPolynomialInt, normalizedPolynomialInt_monic,
    normalizedPolynomialInt_aeval⟩

/-- The normalized generator as an element of the full ring of integers. -/
def normalizedInteger : NumberField.RingOfIntegers M :=
  ⟨normalizedElement, normalizedElement_isIntegral_int⟩

@[simp]
theorem normalizedInteger_coe :
    (normalizedInteger : M) = normalizedElement := rfl

theorem normalizedInteger_aeval :
    Polynomial.aeval normalizedInteger normalizedPolynomialInt = 0 := by
  rw [← RingOfIntegers.coe_eq_zero_iff]
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  simpa only [← IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers M) M, normalizedInteger_coe,
    ← Polynomial.aeval_def] using normalizedPolynomialInt_aeval





end

end MazurTorsion.XOneEighteenTwoDivisionIntegralModel

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralElements. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Integral elements in the `X₁(18)` two-division compositum

This file expresses the explicit descent generators as integer polynomials in
the normalized algebraic integer.  The identities are checked by bounded
polynomial reduction modulo its monic degree-nine equation.  They therefore
do not assume that the normalized power order is the full ring of integers.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralElements

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel

/-- The coefficient-field generator as a reduced polynomial in the
normalized generator. -/
def coefficientPolynomial : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 5 * X ^ 6 + 5 * X ^ 4 -
    2 * X ^ 3 - X ^ 2 + 2 * X - 1

/-- The relative cubic generator as a reduced polynomial in the normalized
generator. -/
def relativePolynomialInNormalized : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 4 * X ^ 6 - 4 * X ^ 5 +
    9 * X ^ 4 + 2 * X ^ 3 - 9 * X ^ 2 + 2 * X + 3

private def coefficientGeneratorNumerator : Polynomial ℚ :=
  1944 - 1944 * X + 2511 * X ^ 2 - 810 * X ^ 3 +
    135 * X ^ 4 + 216 * X ^ 5 - 72 * X ^ 6 - 6 * X ^ 7 + 4 * X ^ 8

private theorem coefficientGeneratorPolynomial_eq :
    coefficientGeneratorPolynomial =
      C (1 / 2673) * coefficientGeneratorNumerator := by
  rfl

private def coefficientReductionQuotient : Polynomial ℚ :=
  4 * X ^ 39 - 116 * X ^ 38 + 1572 * X ^ 37 - 13104 * X ^ 36 +
      74152 * X ^ 35 - 294204 * X ^ 34 + 798830 * X ^ 33 -
      1263102 * X ^ 32 - 49722 * X ^ 31 + 6055080 * X ^ 30 -
      15642084 * X ^ 29 + 14596854 * X ^ 28 + 19949788 * X ^ 27 -
      80612276 * X ^ 26 + 88045260 * X ^ 25 + 51038096 * X ^ 24 -
      264079212 * X ^ 23 + 255207684 * X ^ 22 + 154030532 * X ^ 21 -
      590624884 * X ^ 20 + 397288638 * X ^ 19 + 407446306 * X ^ 18 -
      857304078 * X ^ 17 + 263874420 * X ^ 16 + 664663143 * X ^ 15 -
      718287213 * X ^ 14 - 76011993 * X ^ 13 + 580162460 * X ^ 12 -
      272499070 * X ^ 11 - 202705341 * X ^ 10 + 234062868 * X ^ 9 -
      6549256 * X ^ 8 - 86738118 * X ^ 7 + 30274846 * X ^ 6 +
      13634238 * X ^ 5 - 9014574 * X ^ 4 - 215009 * X ^ 3 +
      680953 * X ^ 2 + 5346 * X + 16679

private theorem coefficientNumerator_comp_inverse_identity :
    coefficientGeneratorNumerator.comp inversePolynomial =
      2673 * coefficientPolynomial +
        coefficientReductionQuotient * normalizedPolynomial := by
  simp only [coefficientGeneratorNumerator, inversePolynomial,
    coefficientPolynomial, coefficientReductionQuotient,
    normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp,
    X_comp, ofNat_comp]
  ring

/-- Reconstruction of the coefficient-field generator from the normalized
integral generator. -/
theorem coefficientGenerator_formula :
    t = Polynomial.aeval normalizedElement coefficientPolynomial := by
  rw [← coefficientGenerator_reconstruction,
    coefficientGeneratorPolynomial_eq, map_mul, aeval_C,
    ← normalizedElement_reconstruction, ← Polynomial.aeval_comp]
  rw [coefficientNumerator_comp_inverse_identity]
  simp only [map_add, map_mul, map_ofNat, normalizedElement_root,
    mul_zero, add_zero]
  rw [map_div₀, map_one, map_ofNat]
  field_simp

/-- Reconstruction of the relative generator from the normalized integral
generator. -/
theorem relativeGenerator_formula :
    s = Polynomial.aeval normalizedElement relativePolynomialInNormalized := by
  calc
    s = t - primitiveElement := by simp only [primitiveElement]; ring
    _ = Polynomial.aeval normalizedElement coefficientPolynomial -
        Polynomial.aeval normalizedElement inversePolynomial := by
      rw [coefficientGenerator_formula, normalizedElement_reconstruction]
    _ = Polynomial.aeval normalizedElement
        (coefficientPolynomial - inversePolynomial) := by rw [map_sub]
    _ = Polynomial.aeval normalizedElement
        relativePolynomialInNormalized := by
      congr 1
      simp only [coefficientPolynomial, inversePolynomial,
        relativePolynomialInNormalized]
      ring

private theorem scaled_aeval_of_reduction (n : ℕ) (hn : n ≠ 0)
    {raw target quotient : Polynomial ℚ}
    (hred : raw = n * target + quotient * normalizedPolynomial) :
    (1 / (n : M)) * Polynomial.aeval normalizedElement raw =
      Polynomial.aeval normalizedElement target := by
  rw [hred]
  simp only [map_add, map_mul, map_natCast, normalizedElement_root,
    mul_zero, add_zero, div_eq_mul_inv, one_mul]
  have hnM : (n : M) ≠ 0 := by exact_mod_cast hn
  rw [← mul_assoc, inv_mul_cancel₀ hnM, one_mul]

/-! ## Integral polynomial representatives -/

/-- Integer polynomial representing `alpha`. -/
def alphaPolynomialInt : Polynomial ℤ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

private def alphaPolynomial : Polynomial ℚ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

theorem alphaPolynomialInt_map :
    alphaPolynomialInt.map (algebraMap ℤ ℚ) = alphaPolynomial := by
  norm_num [alphaPolynomialInt, alphaPolynomial]

private def alphaNumerator : Polynomial ℚ :=
  (2 * coefficientPolynomial ^ 2 - coefficientPolynomial - 1) *
      relativePolynomialInNormalized ^ 2 +
    (-4 * coefficientPolynomial ^ 2 - coefficientPolynomial + 11) *
      relativePolynomialInNormalized +
    (-4 * coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 14)

private def alphaReductionQuotient : Polynomial ℚ :=
  2 * X ^ 23 - 26 * X ^ 22 + 150 * X ^ 21 - 492 * X ^ 20 +
    946 * X ^ 19 - 848 * X ^ 18 - 494 * X ^ 17 + 2212 * X ^ 16 -
    1759 * X ^ 15 - 1699 * X ^ 14 + 4642 * X ^ 13 -
    3073 * X ^ 12 - 1526 * X ^ 11 + 3832 * X ^ 10 -
    1816 * X ^ 9 - 1428 * X ^ 8 + 2503 * X ^ 7 - 1325 * X ^ 6 -
    126 * X ^ 5 + 587 * X ^ 4 - 316 * X ^ 3 + 14 * X ^ 2 +
    78 * X - 50

private theorem alpha_reduction_identity :
    alphaNumerator = 18 * alphaPolynomial +
      alphaReductionQuotient * normalizedPolynomial := by
  simp only [alphaNumerator, alphaPolynomial, alphaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem alpha_formula_rat :
    alpha = Polynomial.aeval normalizedElement alphaPolynomial := by
  calc
    alpha = (1 / 18 : M) *
        Polynomial.aeval normalizedElement alphaNumerator := by
      rw [alpha, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_one, map_neg]
      change ((2 * t ^ 2 - t - 1) / 18) * s ^ 2 +
          ((-4 * t ^ 2 - t + 11) / 18) * s +
          ((-4 * t ^ 2 + 2 * t + 14) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [alphaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_one, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement alphaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        alpha_reduction_identity

/-- The first dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem alpha_formula :
    alpha = Polynomial.aeval normalizedElement alphaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    alphaPolynomialInt, alphaPolynomialInt_map]
  exact alpha_formula_rat

/-- Integer polynomial representing `beta`. -/
def betaPolynomialInt : Polynomial ℤ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

private def betaPolynomial : Polynomial ℚ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

theorem betaPolynomialInt_map :
    betaPolynomialInt.map (algebraMap ℤ ℚ) = betaPolynomial := by
  norm_num [betaPolynomialInt, betaPolynomial]

private def betaNumerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 8) *
      relativePolynomialInNormalized +
    (8 * coefficientPolynomial ^ 2 + 8 * coefficientPolynomial - 10)

private def betaReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2267 * X ^ 13 +
    1412 * X ^ 12 + 937 * X ^ 11 - 2042 * X ^ 10 + 881 * X ^ 9 +
    888 * X ^ 8 - 1403 * X ^ 7 + 580 * X ^ 6 + 387 * X ^ 5 -
    610 * X ^ 4 + 266 * X ^ 3 + 35 * X ^ 2 - 96 * X + 40

private theorem beta_reduction_identity :
    betaNumerator = 18 * betaPolynomial +
      betaReductionQuotient * normalizedPolynomial := by
  simp only [betaNumerator, betaPolynomial, betaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem beta_formula_rat :
    beta = Polynomial.aeval normalizedElement betaPolynomial := by
  calc
    beta = (1 / 18 : M) *
        Polynomial.aeval normalizedElement betaNumerator := by
      rw [beta, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change ((-t ^ 2 + 2 * t + 2) / 18) * s ^ 2 +
          ((-t ^ 2 + 2 * t + 8) / 18) * s +
          ((8 * t ^ 2 + 8 * t - 10) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [betaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement betaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        beta_reduction_identity

/-- The second dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem beta_formula :
    beta = Polynomial.aeval normalizedElement betaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    betaPolynomialInt, betaPolynomialInt_map]
  exact beta_formula_rat

/-- Integer polynomial representing `rho`. -/
def rhoPolynomialInt : Polynomial ℤ :=
  (X - 1) * (3 * X ^ 7 - 8 * X ^ 6 - X ^ 5 + 17 * X ^ 4 -
    6 * X ^ 3 - 19 * X ^ 2 + 2 * X + 6)

private def rhoPolynomial : Polynomial ℚ :=
  (X - 1) * (3 * X ^ 7 - 8 * X ^ 6 - X ^ 5 + 17 * X ^ 4 -
    6 * X ^ 3 - 19 * X ^ 2 + 2 * X + 6)

theorem rhoPolynomialInt_map :
    rhoPolynomialInt.map (algebraMap ℤ ℚ) = rhoPolynomial := by
  norm_num [rhoPolynomialInt, rhoPolynomial]

private def rhoNumerator : Polynomial ℚ :=
  -coefficientPolynomial * relativePolynomialInNormalized ^ 2 +
    (coefficientPolynomial - 2) * relativePolynomialInNormalized +
    (2 * coefficientPolynomial ^ 2 + 2 * coefficientPolynomial - 8)

private def rhoReductionQuotient : Polynomial ℚ :=
  X ^ 15 - 9 * X ^ 14 + 34 * X ^ 13 - 65 * X ^ 12 + 48 * X ^ 11 +
    46 * X ^ 10 - 116 * X ^ 9 + 30 * X ^ 8 + 138 * X ^ 7 -
    176 * X ^ 6 + 63 * X ^ 5 + 33 * X ^ 4 - 28 * X ^ 3 -
    15 * X ^ 2 + 34 * X - 28

private theorem rho_reduction_identity :
    rhoNumerator = 6 * rhoPolynomial +
      rhoReductionQuotient * normalizedPolynomial := by
  simp only [rhoNumerator, rhoPolynomial, rhoReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem rho_formula_rat :
    rho = Polynomial.aeval normalizedElement rhoPolynomial := by
  calc
    rho = (1 / 6 : M) *
        Polynomial.aeval normalizedElement rhoNumerator := by
      rw [rho, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change (-t / 6) * s ^ 2 + ((t - 2) / 6) * s +
          ((2 * t ^ 2 + 2 * t - 8) / 6) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [rhoNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement rhoPolynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        rho_reduction_identity

/-- The triadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem rho_formula :
    rho = Polynomial.aeval normalizedElement rhoPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    rhoPolynomialInt, rhoPolynomialInt_map]
  exact rho_formula_rat































































/-- Integer polynomial representing the integral quotient
`beta² * alpha / 2`. -/
def dyadicQuotientPolynomialInt : Polynomial ℤ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

private def dyadicQuotientPolynomial : Polynomial ℚ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

theorem dyadicQuotientPolynomialInt_map :
    dyadicQuotientPolynomialInt.map (algebraMap ℤ ℚ) =
      dyadicQuotientPolynomial := by
  norm_num [dyadicQuotientPolynomialInt, dyadicQuotientPolynomial]

private def dyadicQuotientReduction : Polynomial ℚ :=
  4 * X ^ 15 - 28 * X ^ 14 + 69 * X ^ 13 - 38 * X ^ 12 -
    131 * X ^ 11 + 210 * X ^ 10 + 74 * X ^ 9 - 364 * X ^ 8 +
    120 * X ^ 7 + 278 * X ^ 6 - 173 * X ^ 5 - 110 * X ^ 4 +
    97 * X ^ 3 + 10 * X ^ 2 - 22 * X + 2

private theorem dyadicQuotient_reduction_identity :
    betaPolynomial ^ 2 * alphaPolynomial =
      2 * dyadicQuotientPolynomial +
        dyadicQuotientReduction * normalizedPolynomial := by
  simp only [betaPolynomial, alphaPolynomial, dyadicQuotientPolynomial,
    dyadicQuotientReduction, normalizedPolynomial]
  ring

private theorem beta_sq_mul_alpha_div_two_formula_rat :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
  calc
    beta ^ 2 * alpha / 2 = (1 / 2 : M) *
        Polynomial.aeval normalizedElement
          (betaPolynomial ^ 2 * alphaPolynomial) := by
      rw [beta_formula_rat, alpha_formula_rat]
      simp only [map_mul, map_pow]
      ring
    _ = Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
      exact scaled_aeval_of_reduction 2 (by norm_num)
        dyadicQuotient_reduction_identity

theorem beta_sq_mul_alpha_div_two_formula :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    dyadicQuotientPolynomialInt, dyadicQuotientPolynomialInt_map]
  exact beta_sq_mul_alpha_div_two_formula_rat

/-- Integer polynomial representing the integral quotient `rho³ / 3`. -/
def triadicQuotientPolynomialInt : Polynomial ℤ :=
  -3 * X ^ 8 + 10 * X ^ 7 - 3 * X ^ 6 - 21 * X ^ 5 +
    17 * X ^ 4 + 21 * X ^ 3 - 17 * X ^ 2 - 11 * X + 3

private def triadicQuotientPolynomial : Polynomial ℚ :=
  -3 * X ^ 8 + 10 * X ^ 7 - 3 * X ^ 6 - 21 * X ^ 5 +
    17 * X ^ 4 + 21 * X ^ 3 - 17 * X ^ 2 - 11 * X + 3

theorem triadicQuotientPolynomialInt_map :
    triadicQuotientPolynomialInt.map (algebraMap ℤ ℚ) =
      triadicQuotientPolynomial := by
  norm_num [triadicQuotientPolynomialInt, triadicQuotientPolynomial]

private def triadicQuotientReduction : Polynomial ℚ :=
  27 * X ^ 15 - 216 * X ^ 14 + 630 * X ^ 13 - 530 * X ^ 12 -
    1200 * X ^ 11 + 2973 * X ^ 10 - 669 * X ^ 9 - 4320 * X ^ 8 +
    3882 * X ^ 7 + 2433 * X ^ 6 - 4476 * X ^ 5 + 87 * X ^ 4 +
    2312 * X ^ 3 - 681 * X ^ 2 - 465 * X + 225

private theorem triadicQuotient_reduction_identity :
    rhoPolynomial ^ 3 = 3 * triadicQuotientPolynomial +
      triadicQuotientReduction * normalizedPolynomial := by
  simp only [rhoPolynomial, triadicQuotientPolynomial,
    triadicQuotientReduction, normalizedPolynomial]
  ring

private theorem rho_cube_div_three_formula_rat :
    rho ^ 3 / 3 =
      Polynomial.aeval normalizedElement triadicQuotientPolynomial := by
  calc
    rho ^ 3 / 3 = (1 / 3 : M) *
        Polynomial.aeval normalizedElement (rhoPolynomial ^ 3) := by
      rw [rho_formula_rat]
      simp only [map_pow]
      ring
    _ = Polynomial.aeval normalizedElement triadicQuotientPolynomial := by
      exact scaled_aeval_of_reduction 3 (by norm_num)
        triadicQuotient_reduction_identity

theorem rho_cube_div_three_formula :
    rho ^ 3 / 3 =
      Polynomial.aeval normalizedElement triadicQuotientPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    triadicQuotientPolynomialInt, triadicQuotientPolynomialInt_map]
  exact rho_cube_div_three_formula_rat

private theorem normalized_aeval_isIntegral (p : Polynomial ℤ) :
    IsIntegral ℤ (Polynomial.aeval normalizedElement p) := by
  rw [← mem_integralClosure_iff]
  have hv : normalizedElement ∈ integralClosure ℤ M :=
    normalizedElement_isIntegral_int
  have hle : Algebra.adjoin ℤ ({normalizedElement} : Set M) ≤
      integralClosure ℤ M :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hv)
  exact hle (Polynomial.aeval_mem_adjoin_singleton ℤ normalizedElement)

theorem alpha_isIntegral : IsIntegral ℤ alpha := by
  rw [alpha_formula]
  exact normalized_aeval_isIntegral alphaPolynomialInt

theorem beta_isIntegral : IsIntegral ℤ beta := by
  rw [beta_formula]
  exact normalized_aeval_isIntegral betaPolynomialInt

theorem rho_isIntegral : IsIntegral ℤ rho := by
  rw [rho_formula]
  exact normalized_aeval_isIntegral rhoPolynomialInt









theorem beta_sq_mul_alpha_div_two_isIntegral :
    IsIntegral ℤ (beta ^ 2 * alpha / 2) := by
  rw [beta_sq_mul_alpha_div_two_formula]
  exact normalized_aeval_isIntegral dyadicQuotientPolynomialInt

theorem rho_cube_div_three_isIntegral :
    IsIntegral ℤ (rho ^ 3 / 3) := by
  rw [rho_cube_div_three_formula]
  exact normalized_aeval_isIntegral triadicQuotientPolynomialInt

/-- The first dyadic generator in the full ring of integers. -/
def alphaInteger : NumberField.RingOfIntegers M := ⟨alpha, alpha_isIntegral⟩

/-- The second dyadic generator in the full ring of integers. -/
def betaInteger : NumberField.RingOfIntegers M := ⟨beta, beta_isIntegral⟩

/-- The triadic generator in the full ring of integers. -/
def rhoInteger : NumberField.RingOfIntegers M := ⟨rho, rho_isIntegral⟩









/-- The integral quotient `beta² * alpha / 2`. -/
def dyadicQuotientInteger : NumberField.RingOfIntegers M :=
  ⟨beta ^ 2 * alpha / 2, beta_sq_mul_alpha_div_two_isIntegral⟩

/-- The integral quotient `rho³ / 3`. -/
def triadicQuotientInteger : NumberField.RingOfIntegers M :=
  ⟨rho ^ 3 / 3, rho_cube_div_three_isIntegral⟩

@[simp] theorem alphaInteger_coe : (alphaInteger : M) = alpha := rfl
@[simp] theorem betaInteger_coe : (betaInteger : M) = beta := rfl
@[simp] theorem rhoInteger_coe : (rhoInteger : M) = rho := rfl




@[simp] theorem dyadicQuotientInteger_coe :
    (dyadicQuotientInteger : M) = beta ^ 2 * alpha / 2 := rfl
@[simp] theorem triadicQuotientInteger_coe :
    (triadicQuotientInteger : M) = rho ^ 3 / 3 := rfl

end

end MazurTorsion.XOneEighteenTwoDivisionIntegralElements

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



/-- The degree-nine compositum has exactly three pairs of complex places. -/
theorem nrComplexPlaces_eq_three : nrComplexPlaces M = 3 :=
  exact_signature.2

end

end MazurTorsion.XOneEighteenTwoDivisionExactSignature

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionMinkowski. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A Minkowski bound for the `X₁(18)` two-division compositum

The normalized integral generator supplies an order of discriminant
`-272097792`.  Comparing its rational basis with an integral basis proves the
required upper bound on the absolute field discriminant; no maximal-order
claim is made.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionMinkowski

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionExactSignature

private def normalizedRootPowerBasis :
    PowerBasis ℚ (AdjoinRoot normalizedPolynomial) :=
  AdjoinRoot.powerBasis normalizedPolynomial_monic.ne_zero

private theorem normalizedPolynomial_derivative_natDegree :
    normalizedPolynomial.derivative.natDegree =
      normalizedPolynomial.natDegree - 1 := by
  have hderiv : normalizedPolynomial.derivative.natDegree = 8 := by
    simp only [normalizedPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
      derivative_one, mul_one, Nat.cast_ofNat, zero_mul, sub_zero]
    compute_degree!
  rw [hderiv, normalizedPolynomial_natDegree]

private theorem normalizedRootPowerBasis_discriminant :
    Algebra.discr ℚ normalizedRootPowerBasis.basis =
      normalizedPolynomial.discr := by
  exact AdjoinRoot.discr_powerBasis_eq_discr normalizedPolynomial_monic
    normalizedPolynomial_derivative_natDegree

private def normalizedDiscriminantBasis :
    Basis (Fin normalizedRootPowerBasis.dim) ℚ M :=
  normalizedRootPowerBasis.basis.map normalizedAdjoinRootEquiv.toLinearEquiv

private theorem normalizedDiscriminantBasis_discriminant :
    Algebra.discr ℚ normalizedDiscriminantBasis = -272097792 := by
  rw [← normalizedPolynomial_discr,
    ← normalizedRootPowerBasis_discriminant]
  calc
    Algebra.discr ℚ normalizedDiscriminantBasis =
        Algebra.discr ℚ
          (normalizedAdjoinRootEquiv ∘ normalizedRootPowerBasis.basis) := by
            congr 1
    _ = Algebra.discr ℚ normalizedRootPowerBasis.basis :=
      (Algebra.discr_eq_discr_of_algEquiv normalizedRootPowerBasis.basis
        normalizedAdjoinRootEquiv).symm

private theorem normalizedDiscriminantBasis_isIntegral
    (i : Fin normalizedRootPowerBasis.dim) :
    IsIntegral ℤ (normalizedDiscriminantBasis i) := by
  rw [normalizedDiscriminantBasis, Basis.map_apply,
    normalizedRootPowerBasis.basis_eq_pow]
  change IsIntegral ℤ
    (normalizedAdjoinRootEquiv (normalizedRootPowerBasis.gen ^ (i : ℕ)))
  rw [map_pow, show normalizedRootPowerBasis.gen =
      AdjoinRoot.root normalizedPolynomial by rfl,
    normalizedAdjoinRootEquiv_root]
  exact normalizedElement_isIntegral_int.pow i

private def reindexedIntegralBasis :
    Basis (Fin normalizedRootPowerBasis.dim) ℚ M :=
  (integralBasis M).reindex
    ((integralBasis M).indexEquiv normalizedDiscriminantBasis)

private theorem reindexedIntegralBasis_discriminant :
    Algebra.discr ℚ reindexedIntegralBasis =
      (NumberField.discr M : ℚ) := by
  simp only [reindexedIntegralBasis, Basis.coe_reindex,
    Algebra.discr_reindex, NumberField.coe_discr]

private theorem changeMatrix_entry_isIntegral
    (i j : Fin normalizedRootPowerBasis.dim) :
    IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis i j) := by
  let x : NumberField.RingOfIntegers M :=
    ⟨normalizedDiscriminantBasis j,
      normalizedDiscriminantBasis_isIntegral j⟩
  let e := (integralBasis M).indexEquiv normalizedDiscriminantBasis
  have hrepr := NumberField.integralBasis_repr_apply (K := M) x (e.symm i)
  rw [Basis.toMatrix_apply]
  change IsIntegral ℤ (reindexedIntegralBasis.repr (x : M) i)
  rw [show reindexedIntegralBasis.repr (x : M) i =
      (integralBasis M).repr (x : M) (e.symm i) by
    simp only [reindexedIntegralBasis, Basis.repr_reindex_apply]
    rfl]
  rw [hrepr]
  exact isIntegral_algebraMap

/-- The absolute field discriminant is bounded by the discriminant of the
explicit normalized integral order. -/
theorem field_discriminant_natAbs_le :
    (NumberField.discr M).natAbs ≤ 272097792 := by
  have hchange :
      Algebra.discr ℚ normalizedDiscriminantBasis =
        (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis).det ^ 2 *
          Algebra.discr ℚ reindexedIntegralBasis := by
    nth_rw 1 [← reindexedIntegralBasis.toMatrix_map_vecMul
      normalizedDiscriminantBasis]
    rw [Algebra.discr_of_matrix_vecMul]
  rw [normalizedDiscriminantBasis_discriminant,
    reindexedIntegralBasis_discriminant] at hchange
  have hdet : IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix normalizedDiscriminantBasis).det :=
    IsIntegral.det changeMatrix_entry_isIntegral
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  rw [← hz] at hchange
  have hint : (-272097792 : ℤ) = z ^ 2 * NumberField.discr M := by
    apply Rat.intCast_inj.mp
    norm_num
    exact hchange
  have hdvd : NumberField.discr M ∣ (-272097792 : ℤ) := by
    exact ⟨z ^ 2, by rw [hint]; ring⟩
  simpa using Int.natAbs_le_of_dvd_ne_zero hdvd
    (by norm_num : (-272097792 : ℤ) ≠ 0)

/-- The classical Minkowski bound for the degree-nine compositum. -/
def minkowskiBound : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
    (Nat.factorial (Module.finrank ℚ M) /
      (Module.finrank ℚ M) ^ (Module.finrank ℚ M) *
        Real.sqrt |NumberField.discr M|)

private theorem abs_discr_cast_le :
    (((|NumberField.discr M| : ℤ) : ℝ)) ≤ 272097792 := by
  have hInt : |NumberField.discr M| ≤ (272097792 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast field_discriminant_natAbs_le
  exact_mod_cast hInt

private theorem sqrt_abs_discr_lt :
    Real.sqrt (((|NumberField.discr M| : ℤ) : ℝ)) < 16500 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16500)]
  nlinarith [abs_discr_cast_le]

/-- The exact Minkowski expression is strictly less than `32`. -/
theorem minkowskiBound_lt_thirtytwo : minkowskiBound < 32 := by
  rw [minkowskiBound, nrComplexPlaces_eq_three, finrank_M_over_rat]
  norm_num [Nat.factorial]
  rw [← Int.cast_abs]
  calc
    (4 / Real.pi) ^ 3 *
        (4480 / 4782969 *
          Real.sqrt (((|NumberField.discr M| : ℤ) : ℝ))) <
      (4 / (3.14 : ℝ)) ^ 3 * (4480 / 4782969 * 16500) := by
        gcongr
        · exact Real.pi_gt_d2
        · exact sqrt_abs_discr_lt
    _ < 32 := by norm_num

end

end MazurTorsion.XOneEighteenTwoDivisionMinkowski

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrincipalSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Principal ideals above the small ramified primes in the `X₁(18)` compositum

The integral quotients constructed in
`XOneEighteenTwoDivisionIntegralElements` are units.  This is verified by
explicit integral Bezout inverses modulo the normalized degree-nine
polynomial.  Consequently the advertised element factorizations give exact
ideal identities

`(2) = (alpha) * (beta)^2` and `(3) = (rho)^3`.

No maximal-order assertion about the normalized power order is used.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## Explicit inverses for the two integral quotients -/

/-- An inverse of `beta^2 * alpha / 2` in the normalized integral order. -/
def dyadicQuotientInversePolynomialInt : Polynomial ℤ :=
  4 * X ^ 8 - 14 * X ^ 7 + 7 * X ^ 6 + 25 * X ^ 5 -
    26 * X ^ 4 - 22 * X ^ 3 + 24 * X ^ 2 + 10 * X - 5

private def dyadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -8 * X ^ 7 + 28 * X ^ 6 - 22 * X ^ 5 - 26 * X ^ 4 +
    44 * X ^ 3 + 7 * X ^ 2 - 15 * X + 6

private theorem dyadicQuotient_bezout_identity :
    dyadicQuotientPolynomialInt * dyadicQuotientInversePolynomialInt =
      1 + dyadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [dyadicQuotientPolynomialInt,
    dyadicQuotientInversePolynomialInt,
    dyadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the dyadic quotient in the full ring of
integers. -/
def dyadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger dyadicQuotientInversePolynomialInt

private theorem dyadicQuotientInteger_eq_aeval :
    dyadicQuotientInteger =
      Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (dyadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger dyadicQuotientPolynomialInt]
  simpa only [dyadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using beta_sq_mul_alpha_div_two_formula

theorem dyadicQuotientInteger_mul_inverse :
    dyadicQuotientInteger * dyadicQuotientInverseInteger = 1 := by
  rw [dyadicQuotientInteger_eq_aeval, dyadicQuotientInverseInteger,
    ← map_mul, dyadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `beta^2 * alpha / 2` is a unit. -/
theorem dyadicQuotientInteger_isUnit : IsUnit dyadicQuotientInteger := by
  exact ⟨⟨dyadicQuotientInteger, dyadicQuotientInverseInteger,
    dyadicQuotientInteger_mul_inverse,
    by rw [mul_comm, dyadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-- An inverse of `rho^3 / 3` in the normalized integral order. -/
def triadicQuotientInversePolynomialInt : Polynomial ℤ :=
  X ^ 8 - 4 * X ^ 7 + 4 * X ^ 6 + 3 * X ^ 5 -
    7 * X ^ 4 - X ^ 3 + 5 * X ^ 2 - 1

private def triadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -3 * X ^ 7 + 13 * X ^ 6 - 16 * X ^ 5 - 5 * X ^ 4 +
    25 * X ^ 3 - 8 * X ^ 2 - 11 * X + 4

private theorem triadicQuotient_bezout_identity :
    triadicQuotientPolynomialInt * triadicQuotientInversePolynomialInt =
      1 + triadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [triadicQuotientPolynomialInt,
    triadicQuotientInversePolynomialInt,
    triadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the triadic quotient in the full ring of
integers. -/
def triadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger triadicQuotientInversePolynomialInt

private theorem triadicQuotientInteger_eq_aeval :
    triadicQuotientInteger =
      Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (triadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger triadicQuotientPolynomialInt]
  simpa only [triadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using rho_cube_div_three_formula

theorem triadicQuotientInteger_mul_inverse :
    triadicQuotientInteger * triadicQuotientInverseInteger = 1 := by
  rw [triadicQuotientInteger_eq_aeval, triadicQuotientInverseInteger,
    ← map_mul, triadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `rho^3 / 3` is a unit. -/
theorem triadicQuotientInteger_isUnit : IsUnit triadicQuotientInteger := by
  exact ⟨⟨triadicQuotientInteger, triadicQuotientInverseInteger,
    triadicQuotientInteger_mul_inverse,
    by rw [mul_comm, triadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-! ## Exact principal-ideal factorizations -/

private theorem dyadic_element_factorization :
    betaInteger ^ 2 * alphaInteger =
      dyadicQuotientInteger * (2 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_mul, map_pow, betaInteger_coe, alphaInteger_coe,
    dyadicQuotientInteger_coe, map_ofNat]
  field_simp

/-- Exact factorization of the rational dyadic ideal in the compositum. -/
theorem span_two_eq_span_alpha_mul_span_beta_sq :
    Ideal.span {(2 : NumberField.RingOfIntegers M)} =
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    mul_comm alphaInteger (betaInteger ^ 2), dyadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit dyadicQuotientInteger_isUnit 2).symm

private theorem triadic_element_factorization :
    rhoInteger ^ 3 =
      triadicQuotientInteger * (3 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_pow, rhoInteger_coe, triadicQuotientInteger_coe, map_mul,
    map_ofNat]
  field_simp

/-- Exact total-cube factorization of the rational triadic ideal in the
compositum. -/
theorem span_three_eq_span_rho_cube :
    Ideal.span {(3 : NumberField.RingOfIntegers M)} =
      Ideal.span {rhoInteger} ^ 3 := by
  rw [Ideal.span_singleton_pow, triadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit triadicQuotientInteger_isUnit 3).symm

/-! ## Absolute norms of the three generators -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]

private theorem absolute_norm_alpha : Algebra.norm ℚ alpha = 8 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := Q.K), norm_alpha]
  change Algebra.norm ℚ (algebraMap ℚ Q.K 2) = 8
  rw [Algebra.norm_algebraMap, coefficientField_finrank]
  norm_num

private theorem integer_norm_alphaInteger :
    Algebra.norm ℤ alphaInteger = 8 := by
  apply Rat.intCast_inj.mp
  rw [Algebra.coe_norm_int]
  simpa only [alphaInteger_coe, Int.cast_ofNat] using absolute_norm_alpha

/-- The first dyadic principal ideal has absolute norm `8`. -/
theorem absNorm_span_alpha :
    Ideal.absNorm (Ideal.span {alphaInteger}) = 8 := by
  rw [Ideal.absNorm_span_singleton, integer_norm_alphaInteger]
  norm_num

/-- The second dyadic principal ideal also has absolute norm `8`. -/
theorem absNorm_span_beta :
    Ideal.absNorm (Ideal.span {betaInteger}) = 8 := by
  have htwo : Ideal.absNorm
      (Ideal.span {(2 : NumberField.RingOfIntegers M)}) = 512 := by
    calc
      Ideal.absNorm
          (Ideal.span {(2 : NumberField.RingOfIntegers M)}) =
        2 ^ Module.finrank ℤ (NumberField.RingOfIntegers M) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers M) 2)
      _ = 512 := by
        rw [RingOfIntegers.rank, finrank_M_over_rat]
        norm_num
  have h := congrArg Ideal.absNorm span_two_eq_span_alpha_mul_span_beta_sq
  rw [htwo, map_mul, map_pow, absNorm_span_alpha] at h
  have hpow : Ideal.absNorm (Ideal.span {betaInteger}) ^ 2 = 8 ^ 2 := by
    norm_num at h ⊢
    omega
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpow



/-! ## Dyadic inertia -/

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_two_irreducible :
    Irreducible (coefficientPolynomialMod 2) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdegree : (coefficientPolynomialMod 2).natDegree = 3 := by
      simp only [coefficientPolynomialMod]
      compute_degree!
    rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    fin_cases z <;> decide

private theorem coefficient_exponent_not_dvd_two :
    ¬ 2 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers Q.K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) (2 : ℤ)).mpr
    (by norm_num)).codisjoint.mono_left hspan

theorem coefficient_inertiaDeg_eq_three_at_two
    (P : Ideal (NumberField.RingOfIntegers Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K)) :
    P.inertiaDeg ℤ = 3 := by
  have hirr : Irreducible
      ((minpoly ℤ coefficientInteger).map (Int.castRingHom (ZMod 2))) := by
    rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod]
    exact coefficientPolynomialMod_two_irreducible
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    coefficient_exponent_not_dvd_two
  have hfactor := (e ⟨P, hP⟩).2
  have hdegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      coefficient_exponent_not_dvd_two hfactor
  simp only [Subtype.coe_eta] at hdegree
  change (e ⟨P, hP⟩ : Polynomial (ZMod 2)) ∈
      (normalizedFactors
        ((minpoly ℤ coefficientInteger).map
          (Int.castRingHom (ZMod 2)))).toFinset at hfactor
  rw [normalizedFactors_irreducible hirr,
    (minpoly.monic coefficientInteger.isIntegral).map
      (Int.castRingHom (ZMod 2)) |>.normalize_eq_self] at hfactor
  simp only [Multiset.toFinset_singleton, Finset.mem_singleton] at hfactor
  rw [hfactor] at hdegree
  have heq := e.symm_apply_apply ⟨P, hP⟩
  have hideal : ((e.symm (e ⟨P, hP⟩)).1 :
      Ideal (NumberField.RingOfIntegers Q.K)) = P :=
    congrArg Subtype.val heq
  rw [hideal] at hdegree
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (coefficientPolynomialMod 2).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree

/-- Every prime of the compositum above `2` has inertia degree at least
three. -/
theorem compositum_inertiaDeg_ge_three_at_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  let QP : Ideal (NumberField.RingOfIntegers Q.K) :=
    P.under (NumberField.RingOfIntegers Q.K)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K) := ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three_at_two QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ)
    ⟨P.inertiaDeg (NumberField.RingOfIntegers Q.K), htower⟩

/-- Every prime of the compositum above `2` has absolute norm at least
`8`. -/
theorem eight_le_absNorm_of_mem_primesOver_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    8 ≤ P.absNorm := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg 2 P]
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ))
    (compositum_inertiaDeg_ge_three_at_two P hP)

private theorem eq_of_dvd_of_eight_le_absNorm
    {P I : Ideal (NumberField.RingOfIntegers M)}
    (hdiv : P ∣ I) (hP : 8 ≤ P.absNorm) (hI : I.absNorm = 8) :
    P = I := by
  have hle : I ≤ P := Ideal.dvd_iff_le.mp hdiv
  have hnormDvd : P.absNorm ∣ I.absNorm :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  have hPupper : P.absNorm ≤ 8 := by
    rw [← hI]
    exact Nat.le_of_dvd (hI.symm ▸ by norm_num) hnormDvd
  have hPnorm : P.absNorm = 8 := le_antisymm hPupper hP
  obtain ⟨J, hJ⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, hPnorm, hI] at hnorm
  have hJnorm : J.absNorm = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  rw [hJtop, mul_top] at hJ
  exact hJ.symm

/-- The two displayed principal ideals are all the primes of the compositum
above `2`. -/
theorem prime_over_two_eq_span_alpha_or_beta
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    P = Ideal.span {alphaInteger} ∨ P = Ideal.span {betaInteger} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have hPtwo : P ∣ Ideal.span
      {(2 : NumberField.RingOfIntegers M)} := by
    have hmap :=
      (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  have hprod : P ∣
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
    rw [← span_two_eq_span_alpha_mul_span_beta_sq]
    exact hPtwo
  have hlower := eight_le_absNorm_of_mem_primesOver_two P hP
  rcases hprime.dvd_or_dvd hprod with hAlpha | hBetaSq
  · exact Or.inl
      (eq_of_dvd_of_eight_le_absNorm hAlpha hlower absNorm_span_alpha)
  · have hBeta : P ∣ Ideal.span {betaInteger} :=
      hprime.dvd_of_dvd_pow hBetaSq
    exact Or.inr
      (eq_of_dvd_of_eight_le_absNorm hBeta hlower absNorm_span_beta)

end

end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicPrime. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The triadic prime in the `X₁(18)` two-division compositum

We first identify the unique prime above `3` in the real cubic coefficient
field.  The normalized generator then has a relative cubic polynomial of
discriminant `-8`; its irreducible reduction at that coefficient prime gives
the unique prime above `3` in the degree-nine compositum.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicPrime

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The unique coefficient-field prime above `3` -/

/-- A uniformizer above `3` in the real cubic coefficient field. -/
def coefficientTriadicUniformizer : NumberField.RingOfIntegers Q.K :=
  coefficientInteger - 1

private def coefficientTriadicUnit : NumberField.RingOfIntegers Q.K :=
  2 * coefficientInteger - coefficientInteger ^ 2

private def coefficientTriadicUnitInverse : NumberField.RingOfIntegers Q.K :=
  coefficientInteger ^ 2 + coefficientInteger - 1

private theorem coefficientTriadicUnit_mul_inverse :
    coefficientTriadicUnit * coefficientTriadicUnitInverse = 1 := by
  apply RingOfIntegers.coe_injective
  change (2 * Q.tau - Q.tau ^ 2) *
      (Q.tau ^ 2 + Q.tau - 1) = 1
  linear_combination (1 - Q.tau) * Q.tau_cubic

private theorem coefficientTriadicUnit_isUnit :
    IsUnit coefficientTriadicUnit := by
  exact ⟨⟨coefficientTriadicUnit, coefficientTriadicUnitInverse,
    coefficientTriadicUnit_mul_inverse,
    by rw [mul_comm, coefficientTriadicUnit_mul_inverse]⟩, rfl⟩

private theorem coefficientTriadic_element_factorization :
    coefficientTriadicUniformizer ^ 3 =
      (3 : NumberField.RingOfIntegers Q.K) * coefficientTriadicUnit := by
  apply RingOfIntegers.coe_injective
  change (Q.tau - 1) ^ 3 = 3 * (2 * Q.tau - Q.tau ^ 2)
  linear_combination Q.tau_cubic

/-- The rational triadic ideal is the cube of the displayed coefficient
prime. -/
theorem coefficient_span_three_eq_uniformizer_cube :
    Ideal.span {(3 : NumberField.RingOfIntegers Q.K)} =
      Ideal.span {coefficientTriadicUniformizer} ^ 3 := by
  rw [Ideal.span_singleton_pow, coefficientTriadic_element_factorization,
    mul_comm (3 : NumberField.RingOfIntegers Q.K) coefficientTriadicUnit]
  exact (Ideal.span_singleton_mul_left_unit coefficientTriadicUnit_isUnit 3).symm

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]

/-- The coefficient-field uniformizer ideal has absolute norm `3`. -/
theorem coefficientTriadicPrime_absNorm :
    Ideal.absNorm (Ideal.span {coefficientTriadicUniformizer}) = 3 := by
  have hthree : Ideal.absNorm
      (Ideal.span {(3 : NumberField.RingOfIntegers Q.K)}) = 27 := by
    calc
      Ideal.absNorm
          (Ideal.span {(3 : NumberField.RingOfIntegers Q.K)}) =
        3 ^ Module.finrank ℤ (NumberField.RingOfIntegers Q.K) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers Q.K) 3)
      _ = 27 := by
        rw [RingOfIntegers.rank, coefficientField_finrank]
        norm_num
  have h := congrArg Ideal.absNorm
    coefficient_span_three_eq_uniformizer_cube
  rw [hthree, map_pow] at h
  have hpow :
      Ideal.absNorm (Ideal.span {coefficientTriadicUniformizer}) ^ 3 =
        3 ^ 3 := by
    norm_num at h ⊢
    exact h.symm
  exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hpow

/-- The displayed norm-three ideal is prime. -/
theorem coefficientTriadicPrime_isPrime :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [coefficientTriadicPrime_absNorm]
  exact (Nat.irreducible_iff_nat_prime 3).mpr Nat.prime_three







end

end MazurTorsion.XOneEighteenTwoDivisionTriadicPrime

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicLift. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The triadic prime in the `X₁(18)` two-division compositum

The normalized integral generator has a relative cubic polynomial over the
real cubic coefficient field.  Its discriminant is `-8`, so reduction at the
unique coefficient prime above `3` is controlled by Kummer--Dedekind.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The relative normalized polynomial -/

/-- The relative cubic polynomial of the normalized generator over the
coefficient field. -/
def normalizedRelativePolynomial : Polynomial Q.K :=
  X ^ 3 + C (Q.tau ^ 2 - 3) * X ^ 2 +
    C (-2 * Q.tau ^ 2 + Q.tau + 4) * X - 1

theorem normalizedRelativePolynomial_monic :
    normalizedRelativePolynomial.Monic := by
  simp only [normalizedRelativePolynomial]
  monicity <;> norm_num

theorem normalizedRelativePolynomial_natDegree :
    normalizedRelativePolynomial.natDegree = 3 := by
  simp only [normalizedRelativePolynomial]
  compute_degree!

private def normalizedRelativeExpression : Polynomial ℚ :=
  X ^ 3 + (coefficientPolynomial ^ 2 - 3) * X ^ 2 +
    (-2 * coefficientPolynomial ^ 2 + coefficientPolynomial + 4) * X - 1

private def normalizedRelativeReductionQuotient : Polynomial ℚ :=
  X ^ 9 - 7 * X ^ 8 + 21 * X ^ 7 - 36 * X ^ 6 +
    39 * X ^ 5 - 28 * X ^ 4 + 13 * X ^ 3 -
    2 * X ^ 2 - X + 1

private theorem normalizedRelative_reduction_identity :
    normalizedRelativeExpression =
      normalizedRelativeReductionQuotient * normalizedPolynomial := by
  simp only [normalizedRelativeExpression,
    normalizedRelativeReductionQuotient, coefficientPolynomial,
    normalizedPolynomial]
  ring

private theorem normalizedRelativeExpression_root :
    Polynomial.aeval normalizedElement normalizedRelativeExpression = 0 := by
  rw [normalizedRelative_reduction_identity]
  simp only [map_mul, normalizedElement_root, mul_zero]

/-- The normalized generator satisfies the displayed relative cubic. -/
theorem normalizedElement_relative_root :
    Polynomial.aeval normalizedElement normalizedRelativePolynomial = 0 := by
  simp only [normalizedRelativePolynomial, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_C, map_neg, map_one, map_ofNat]
  change normalizedElement ^ 3 +
      (t ^ 2 - 3) * normalizedElement ^ 2 +
      (-2 * t ^ 2 + t + 4) * normalizedElement - 1 = 0
  rw [coefficientGenerator_formula]
  simpa only [normalizedRelativeExpression, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_neg, map_one, aeval_X] using
    normalizedRelativeExpression_root

/-- The normalized generator also generates the compositum over the
coefficient field. -/
theorem normalizedElement_adjoin_coefficient_eq_top :
    Algebra.adjoin Q.K ({normalizedElement} : Set M) = ⊤ := by
  apply top_unique
  intro z hz
  have hzRat : z ∈ Algebra.adjoin ℚ ({normalizedElement} : Set M) := by
    rw [normalizedElement_adjoin_eq_top]
    trivial
  have hle : Algebra.adjoin ℚ ({normalizedElement} : Set M) ≤
      (Algebra.adjoin Q.K ({normalizedElement} : Set M)).restrictScalars ℚ := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Algebra.subset_adjoin (R := Q.K) (Set.mem_singleton normalizedElement)
  exact hle hzRat

private def normalizedRelativePowerBasis : PowerBasis Q.K M :=
  PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite Q.K normalizedElement)
    normalizedElement_adjoin_coefficient_eq_top

@[simp]
private theorem normalizedRelativePowerBasis_gen :
    normalizedRelativePowerBasis.gen = normalizedElement := by
  rw [normalizedRelativePowerBasis, PowerBasis.ofAdjoinEqTop_gen]

private theorem normalizedElement_relative_minpoly_natDegree :
    (minpoly Q.K normalizedElement).natDegree = 3 := by
  calc
    (minpoly Q.K normalizedElement).natDegree =
        normalizedRelativePowerBasis.dim := by
      simpa only [normalizedRelativePowerBasis_gen] using
        normalizedRelativePowerBasis.natDegree_minpoly
    _ = Module.finrank Q.K M := normalizedRelativePowerBasis.finrank.symm
    _ = 3 := finrank_M_over_K

/-- The displayed relative cubic is exactly the minimal polynomial of the
normalized generator over the coefficient field. -/
theorem normalizedElement_minpoly_relative :
    minpoly Q.K normalizedElement = normalizedRelativePolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite Q.K normalizedElement))
    normalizedRelativePolynomial_monic
    (minpoly.dvd Q.K normalizedElement normalizedElement_relative_root)
    (by rw [normalizedRelativePolynomial_natDegree,
      normalizedElement_relative_minpoly_natDegree])).symm

theorem normalizedRelativePolynomial_irreducible :
    Irreducible normalizedRelativePolynomial := by
  rw [← normalizedElement_minpoly_relative]
  exact minpoly.irreducible (IsIntegral.of_finite Q.K normalizedElement)

private instance normalizedRelativePolynomial_irreducibleFact :
    Fact (Irreducible normalizedRelativePolynomial) :=
  ⟨normalizedRelativePolynomial_irreducible⟩

/-- The relative cubic has discriminant `-8`. -/
theorem normalizedRelativePolynomial_discriminant :
    normalizedRelativePolynomial.discr = -8 := by
  have hcoeffZero : normalizedRelativePolynomial.coeff 0 = -1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffOne : normalizedRelativePolynomial.coeff 1 =
      -2 * Q.tau ^ 2 + Q.tau + 4 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffTwo : normalizedRelativePolynomial.coeff 2 =
      Q.tau ^ 2 - 3 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffThree : normalizedRelativePolynomial.coeff 3 = 1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  rw [Polynomial.discr_of_degree_eq_three]
  · rw [hcoeffZero, hcoeffOne, hcoeffTwo, hcoeffThree]
    ring_nf
    linear_combination
      (4 * Q.tau ^ 5 - 4 * Q.tau ^ 4 + 9 * Q.tau ^ 3 -
        24 * Q.tau ^ 2 - 3 * Q.tau + 23) * Q.tau_cubic
  · rw [degree_eq_natDegree normalizedRelativePolynomial_monic.ne_zero,
      normalizedRelativePolynomial_natDegree]
    norm_num

/-! ## A relative power basis with discriminant `-8` -/

private theorem normalizedRelativeRoot_satisfies_minpoly :
    Polynomial.aeval (AdjoinRoot.root normalizedRelativePolynomial)
      (minpoly Q.K normalizedRelativePowerBasis.gen) = 0 := by
  rw [normalizedRelativePowerBasis_gen,
    normalizedElement_minpoly_relative]
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root normalizedRelativePolynomial

private theorem normalizedRelativePowerBasis_root :
    Polynomial.aeval normalizedRelativePowerBasis.gen
      normalizedRelativePolynomial = 0 := by
  rw [normalizedRelativePowerBasis_gen]
  exact normalizedElement_relative_root

private def normalizedRelativeAdjoinRootEquiv :
    AdjoinRoot normalizedRelativePolynomial ≃ₐ[Q.K] M :=
  AdjoinRoot.equiv' normalizedRelativePolynomial normalizedRelativePowerBasis
    normalizedRelativeRoot_satisfies_minpoly
    normalizedRelativePowerBasis_root

@[simp]
private theorem normalizedRelativeAdjoinRootEquiv_root :
    normalizedRelativeAdjoinRootEquiv
        (AdjoinRoot.root normalizedRelativePolynomial) =
      normalizedElement := by
  change normalizedRelativeAdjoinRootEquiv.toAlgHom
      (AdjoinRoot.root normalizedRelativePolynomial) = normalizedElement
  rw [normalizedRelativeAdjoinRootEquiv, AdjoinRoot.equiv'_toAlgHom]
  calc
    _ = normalizedRelativePowerBasis.gen :=
      AdjoinRoot.liftAlgHom_root normalizedRelativePolynomial _ _ _
    _ = normalizedElement := normalizedRelativePowerBasis_gen

private def normalizedRelativeRootPowerBasis :
    PowerBasis Q.K (AdjoinRoot normalizedRelativePolynomial) :=
  AdjoinRoot.powerBasis normalizedRelativePolynomial_monic.ne_zero

private theorem normalizedRelativePolynomial_derivative_natDegree :
    normalizedRelativePolynomial.derivative.natDegree =
      normalizedRelativePolynomial.natDegree - 1 := by
  have hderivative : normalizedRelativePolynomial.derivative.natDegree = 2 := by
    simp only [normalizedRelativePolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_C,
      zero_mul, mul_one, Nat.cast_ofNat, derivative_one, sub_zero]
    compute_degree!
  rw [hderivative, normalizedRelativePolynomial_natDegree]

private theorem normalizedRelativeRootPowerBasis_discriminant :
    Algebra.discr Q.K normalizedRelativeRootPowerBasis.basis =
      normalizedRelativePolynomial.discr := by
  letI : Module.Finite Q.K (AdjoinRoot normalizedRelativePolynomial) :=
    normalizedRelativePolynomial_monic.finite_adjoinRoot
  letI : Algebra.IsAlgebraic Q.K
      (AdjoinRoot normalizedRelativePolynomial) :=
    ⟨fun x ↦ (IsIntegral.of_finite Q.K x).isAlgebraic⟩
  letI : Algebra.IsSeparable Q.K
      (AdjoinRoot normalizedRelativePolynomial) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AdjoinRoot.discr_powerBasis_eq_discr
    normalizedRelativePolynomial_monic
    normalizedRelativePolynomial_derivative_natDegree

/-- A relative power basis of the compositum, obtained from the explicit
relative cubic presentation. -/
def normalizedRelativeMappedPowerBasis : PowerBasis Q.K M :=
  normalizedRelativeRootPowerBasis.map normalizedRelativeAdjoinRootEquiv

@[simp]
theorem normalizedRelativeMappedPowerBasis_gen :
    normalizedRelativeMappedPowerBasis.gen = normalizedElement := by
  rw [normalizedRelativeMappedPowerBasis, PowerBasis.map_gen,
    normalizedRelativeRootPowerBasis, AdjoinRoot.powerBasis_gen,
    normalizedRelativeAdjoinRootEquiv_root]

/-- The explicit relative power basis has discriminant `-8`. -/
theorem normalizedRelativeMappedPowerBasis_discriminant :
    Algebra.discr Q.K normalizedRelativeMappedPowerBasis.basis = -8 := by
  rw [← normalizedRelativePolynomial_discriminant,
    ← normalizedRelativeRootPowerBasis_discriminant]
  exact (Algebra.discr_eq_discr_of_algEquiv
    normalizedRelativeRootPowerBasis.basis
    normalizedRelativeAdjoinRootEquiv).symm

/-! ## The integral relative polynomial -/

/-- The same relative polynomial over the coefficient ring of integers. -/
def normalizedRelativePolynomialInteger :
    Polynomial (NumberField.RingOfIntegers Q.K) :=
  X ^ 3 + C (coefficientInteger ^ 2 - 3) * X ^ 2 +
    C (-2 * coefficientInteger ^ 2 + coefficientInteger + 4) * X - 1



theorem normalizedRelativePolynomialInteger_map :
    normalizedRelativePolynomialInteger.map
        (algebraMap (NumberField.RingOfIntegers Q.K) Q.K) =
      normalizedRelativePolynomial := by
  have hcoefficient :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K
          coefficientInteger = Q.tau := rfl
  have htwo :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 2 = 2 := by
    exact map_ofNat _ 2
  have hthree :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 3 = 3 := by
    exact map_ofNat _ 3
  have hfour :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 4 = 4 := by
    exact map_ofNat _ 4
  simp [normalizedRelativePolynomialInteger,
    normalizedRelativePolynomial, hcoefficient, htwo, hthree, hfour]

/-- The displayed integral cubic is the minimal polynomial of the normalized
integer over the coefficient ring of integers. -/
theorem normalizedInteger_minpoly_relative :
    minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger =
      normalizedRelativePolynomialInteger := by
  apply Polynomial.map_injective
    (algebraMap (NumberField.RingOfIntegers Q.K) Q.K)
    RingOfIntegers.coe_injective
  rw [normalizedRelativePolynomialInteger_map]
  have hInt : IsIntegral (NumberField.RingOfIntegers Q.K)
      normalizedInteger :=
    Algebra.IsIntegral.isIntegral (R := NumberField.RingOfIntegers Q.K)
      normalizedInteger
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions Q.K M
    hInt
  rw [← hfield]
  change minpoly Q.K normalizedElement = normalizedRelativePolynomial
  exact normalizedElement_minpoly_relative

/-! ## Relative conductor control at the coefficient prime -/

/-- The relative discriminant belongs to the conductor of the normalized
integral order. -/
theorem relative_discriminant_mem_conductor :
    algebraMap (NumberField.RingOfIntegers Q.K)
        (NumberField.RingOfIntegers M) (-8) ∈
      conductor (NumberField.RingOfIntegers Q.K) normalizedInteger := by
  have hfield :
      algebraMap (NumberField.RingOfIntegers M) M
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M) (-8)) ∈
        IsLocalization.coeSubmodule M
          (conductor (NumberField.RingOfIntegers Q.K)
            normalizedInteger) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hgen : IsIntegral (NumberField.RingOfIntegers Q.K)
        normalizedRelativeMappedPowerBasis.gen := by
      rw [normalizedRelativeMappedPowerBasis_gen]
      exact normalizedElement_isIntegral_int.tower_top
    have hz : IsIntegral (NumberField.RingOfIntegers Q.K) (z : M) :=
      (RingOfIntegers.isIntegral_coe z).tower_top
    have hdisc := Algebra.discr_mul_isIntegral_mem_adjoin Q.K
      (B := normalizedRelativeMappedPowerBasis) hgen hz
    rw [normalizedRelativeMappedPowerBasis_discriminant] at hdisc
    simpa only [normalizedRelativeMappedPowerBasis_gen,
      normalizedInteger_coe, Algebra.smul_def,
      RingOfIntegers.coe_eq_algebraMap, map_intCast, map_neg, map_ofNat,
      IsScalarTower.algebraMap_apply ℤ Q.K M,
      IsScalarTower.algebraMap_apply
        (NumberField.RingOfIntegers Q.K)
        (NumberField.RingOfIntegers M) M] using hdisc
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule M
      (conductor (NumberField.RingOfIntegers Q.K)
        normalizedInteger)).mp hfield
  have hz' : z = algebraMap (NumberField.RingOfIntegers Q.K)
      (NumberField.RingOfIntegers M) (-8) :=
    RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The normalized relative order has conductor coprime to the unique
coefficient prime above `3`. -/
theorem relative_conductor_coprime_at_three :
    (conductor (NumberField.RingOfIntegers Q.K) normalizedInteger).comap
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M)) ⊔
        Ideal.span {coefficientTriadicUniformizer} = ⊤ := by
  let I : Ideal (NumberField.RingOfIntegers Q.K) :=
    Ideal.span {coefficientTriadicUniformizer}
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hnorm := coefficientTriadicPrime_absNorm
    change Ideal.absNorm I = 3 at hnorm
    rw [hbot, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm
  have hImax : I.IsMaximal :=
    coefficientTriadicPrime_isPrime.isMaximal hIne
  have hminusEightComap :
      (-8 : NumberField.RingOfIntegers Q.K) ∈
        (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) :=
    relative_discriminant_mem_conductor
  have hthree : (3 : NumberField.RingOfIntegers Q.K) ∈ I := by
    apply (Ideal.span_singleton_le_iff_mem I).mp
    rw [coefficient_span_three_eq_uniformizer_cube]
    exact Ideal.pow_le_self (by norm_num)
  have hminusEightNot :
      (-8 : NumberField.RingOfIntegers Q.K) ∉ I := by
    intro hminusEight
    have hnine : (9 : NumberField.RingOfIntegers Q.K) ∈ I := by
      convert I.mul_mem_left 3 hthree using 1
      norm_num
    have hone : (1 : NumberField.RingOfIntegers Q.K) ∈ I := by
      convert I.add_mem hnine hminusEight using 1
      norm_num
    exact coefficientTriadicPrime_isPrime.ne_top
      ((Ideal.eq_top_iff_one I).mpr hone)
  by_contra hsup
  have heq : I =
      (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) ⊔ I :=
    hImax.eq_of_le hsup le_sup_right
  apply hminusEightNot
  have hle :
      (conductor (NumberField.RingOfIntegers Q.K)
          normalizedInteger).comap
            (algebraMap (NumberField.RingOfIntegers Q.K)
              (NumberField.RingOfIntegers M)) ≤ I := by
    rw [heq]
    exact le_sup_left
  exact hle hminusEightComap

/-! ## Irreducible reduction at the triadic coefficient prime -/

private theorem coefficientTriadicIdeal_ne_bot :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)) ≠ ⊥ := by
  intro hbot
  have hnorm := coefficientTriadicPrime_absNorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private instance coefficientTriadicIdeal_isMaximal :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).IsMaximal :=
  coefficientTriadicPrime_isPrime.isMaximal coefficientTriadicIdeal_ne_bot

/-- The residue field of the coefficient field at its unique triadic prime. -/
abbrev CoefficientTriadicResidue :=
  NumberField.RingOfIntegers Q.K ⧸
    Ideal.span {coefficientTriadicUniformizer}

noncomputable instance coefficientTriadicResidue_fintype :
    Fintype CoefficientTriadicResidue := Fintype.ofFinite _

private theorem coefficientTriadicResidue_card :
    Fintype.card CoefficientTriadicResidue = 3 := by
  rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply]
  exact coefficientTriadicPrime_absNorm

/-- The coefficient residue field is canonically identified with `ZMod 3`. -/
noncomputable def coefficientTriadicResidueEquiv :
    ZMod 3 ≃+* CoefficientTriadicResidue :=
  ZMod.ringEquivOfPrime CoefficientTriadicResidue Nat.prime_three
    coefficientTriadicResidue_card

private instance coefficientTriadicResidue_charP :
    CharP CoefficientTriadicResidue 3 :=
  CharP.of_ringHom_of_ne_zero
    coefficientTriadicResidueEquiv.toRingHom 3 (by norm_num)

private theorem coefficientInteger_mod_triadic :
    Ideal.Quotient.mk (Ideal.span {coefficientTriadicUniformizer})
        coefficientInteger = 1 := by
  apply Ideal.Quotient.eq.mpr
  change coefficientInteger - 1 ∈
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K))
  exact Ideal.mem_span_singleton_self coefficientTriadicUniformizer

/-- The irreducible cubic obtained by reducing the relative polynomial at
the coefficient prime above `3`. -/
def triadicResiduePolynomial : Polynomial (ZMod 3) :=
  X ^ 3 + X ^ 2 - 1

theorem triadicResiduePolynomial_irreducible :
    Irreducible triadicResiduePolynomial := by
  have hdegree : triadicResiduePolynomial.natDegree = 3 := by
    simp only [triadicResiduePolynomial]
    compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := triadicResiduePolynomial) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [triadicResiduePolynomial, eval_sub, eval_add, eval_pow,
      eval_X, eval_one]
    fin_cases z <;> decide

/-- Exact reduction of the relative integral minimal polynomial at the
triadic coefficient prime. -/
theorem normalizedInteger_minpoly_mod_triadic :
    Polynomial.map
        (Ideal.Quotient.mk
          (Ideal.span {coefficientTriadicUniformizer}))
        (minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger) =
      Polynomial.mapEquiv coefficientTriadicResidueEquiv
        triadicResiduePolynomial := by
  rw [normalizedInteger_minpoly_relative]
  simp only [normalizedRelativePolynomialInteger,
    triadicResiduePolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X,
    Polynomial.map_C, Polynomial.mapEquiv_apply]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  rw [coefficientInteger_mod_triadic]
  simp only [one_pow, mul_one, C_1]
  linear_combination
    (X - X ^ 2) *
      (CharP.cast_eq_zero (Polynomial CoefficientTriadicResidue) 3)

/-- The reduced relative minimal polynomial is irreducible. -/
theorem normalizedInteger_minpoly_mod_triadic_irreducible :
    Irreducible
      (Polynomial.map
        (Ideal.Quotient.mk
          (Ideal.span {coefficientTriadicUniformizer}))
        (minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger)) := by
  rw [normalizedInteger_minpoly_mod_triadic]
  exact triadicResiduePolynomial_irreducible.map
    (Polynomial.mapEquiv coefficientTriadicResidueEquiv)

/-! ## The unique triadic prime in the compositum -/

/-- The coefficient prime remains irreducible after extension to the
compositum. -/
theorem coefficientTriadicIdeal_map_irreducible :
    Irreducible
      ((Ideal.span {coefficientTriadicUniformizer} :
        Ideal (NumberField.RingOfIntegers Q.K)).map
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M))) := by
  exact KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly
    coefficientTriadicIdeal_isMaximal coefficientTriadicIdeal_ne_bot
    relative_conductor_coprime_at_three
    (Algebra.IsIntegral.isIntegral
      (R := NumberField.RingOfIntegers Q.K) normalizedInteger)
    normalizedInteger_minpoly_mod_triadic_irreducible

/-- The extended coefficient prime is a prime ideal of the compositum. -/
theorem coefficientTriadicIdeal_map_isPrime :
    ((Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).map
        (algebraMap (NumberField.RingOfIntegers Q.K)
          (NumberField.RingOfIntegers M))).IsPrime := by
  apply Ideal.isPrime_of_prime
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    coefficientTriadicIdeal_map_irreducible

/-- Extending the coefficient prime gives exactly the principal ideal
generated by `rho`. -/
theorem coefficientTriadicIdeal_map_eq_span_rho :
    (Ideal.span {coefficientTriadicUniformizer} :
      Ideal (NumberField.RingOfIntegers Q.K)).map
        (algebraMap (NumberField.RingOfIntegers Q.K)
          (NumberField.RingOfIntegers M)) =
      Ideal.span {rhoInteger} := by
  have hmap := congrArg
    (Ideal.map (algebraMap (NumberField.RingOfIntegers Q.K)
      (NumberField.RingOfIntegers M)))
    coefficient_span_three_eq_uniformizer_cube
  have hcubes :
      ((Ideal.span {coefficientTriadicUniformizer} :
        Ideal (NumberField.RingOfIntegers Q.K)).map
          (algebraMap (NumberField.RingOfIntegers Q.K)
            (NumberField.RingOfIntegers M))) ^ 3 =
        Ideal.span {rhoInteger} ^ 3 := by
    calc
      _ = Ideal.span {(3 : NumberField.RingOfIntegers M)} := by
        symm
        simpa only [Ideal.map_span, Set.image_singleton, map_ofNat,
          Ideal.map_pow] using hmap
      _ = Ideal.span {rhoInteger} ^ 3 :=
        span_three_eq_span_rho_cube
  exact pow_left_injective (by norm_num : 3 ≠ 0) hcubes

/-- Every prime of the compositum above `3` is the displayed principal
ideal generated by `rho`. -/
theorem compositum_prime_over_three_eq_span_rho
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(3 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    P = Ideal.span {rhoInteger} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(3 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 3
  have hPthree : P ∣
      Ideal.span {(3 : NumberField.RingOfIntegers M)} := by
    have hmap := (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  rw [span_three_eq_span_rho_cube] at hPthree
  have hPrho : P ∣ Ideal.span {rhoInteger} :=
    hprime.dvd_of_dvd_pow hPthree
  have hspanPrime : (Ideal.span {rhoInteger} :
      Ideal (NumberField.RingOfIntegers M)).IsPrime := by
    rw [← coefficientTriadicIdeal_map_eq_span_rho]
    exact coefficientTriadicIdeal_map_isPrime
  have hspanNeBot : (Ideal.span {rhoInteger} :
      Ideal (NumberField.RingOfIntegers M)) ≠ ⊥ := by
    rw [← coefficientTriadicIdeal_map_eq_span_rho]
    exact (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      coefficientTriadicIdeal_map_irreducible).ne_zero
  exact (hspanPrime.isMaximal hspanNeBot).eq_of_le hP.1.ne_top
    (Ideal.dvd_iff_le.mp hPrho) |>.symm

end

end MazurTorsion.XOneEighteenTwoDivisionTriadicLift

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumberOne. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Class number one for the `X₁(18)` two-division compositum

The exact Minkowski bound is less than `32`.  The primes over `2` are the
two displayed principal dyadic ideals, the unique prime over `3` is generated
by `rho`, and the checked inertia certificates exclude every rational prime
between `5` and `31`.  These facts prove that the full ring of integers is a
principal ideal ring.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumberOne

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionMinkowski
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift
open NumberField Ideal RingOfIntegers

/-- The full ring of integers of the degree-nine two-division compositum is
a principal ideal ring. -/
theorem compositumRingOfIntegers_isPrincipal :
    IsPrincipalIdealRing (NumberField.RingOfIntegers M) := by
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpRange hpPrime P hP hpow
  have hfloor :
      ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
          (Nat.factorial (Module.finrank ℚ M) /
            (Module.finrank ℚ M) ^ (Module.finrank ℚ M) *
              Real.sqrt |NumberField.discr M|)⌋₊ ≤ 31 := by
    change ⌊minkowskiBound⌋₊ ≤ 31
    have hlt : ⌊minkowskiBound⌋₊ < 32 :=
      (Nat.floor_lt' (by norm_num : 32 ≠ 0)).mpr
        minkowskiBound_lt_thirtytwo
    omega
  have hpUpper : p ≤ 31 :=
    (Finset.mem_Icc.mp hpRange).2.trans hfloor
  by_cases hpTwo : p = 2
  · subst p
    rcases prime_over_two_eq_span_alpha_or_beta P hP with hAlpha | hBeta
    · rw [hAlpha]
      infer_instance
    · rw [hBeta]
      infer_instance
  by_cases hpThree : p = 3
  · subst p
    rw [compositum_prime_over_three_eq_span_rho P hP]
    infer_instance
  have hpLower : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hpPrime.eq_two_or_odd'.resolve_left hpTwo
    have hpTwoLe : 2 ≤ p := hpPrime.two_le
    omega
  have hlarge := thirtyone_lt_absNorm_of_mem_primesOver p
    (Finset.mem_Icc.mpr ⟨hpLower, hpUpper⟩) hpPrime P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg p P] at hlarge
  omega



end

end MazurTorsion.XOneEighteenTwoDivisionClassNumberOne

end

theorem solution :
IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M) := by
  exact MazurTorsion.XOneEighteenTwoDivisionClassNumberOne.compositumRingOfIntegers_isPrincipal

#print axioms solution
end
