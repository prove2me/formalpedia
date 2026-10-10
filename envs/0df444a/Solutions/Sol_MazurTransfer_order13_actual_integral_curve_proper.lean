-- Prove2me | solution 1 for MazurTransfer.order13_actual_integral_curve_proper
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T02:18:51.505187+00:00
-- url     : https://prove2.me/submissions/81beb2d7-2de0-44f0-9d1c-6aeb2329dc67

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Per-file source attribution is retained below.
Design boundary: properness of the actual literal glued integral curve
without field or characteristic hypotheses. Named downstream consumer:
the smooth proper integral curve and compatible Picard family.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve


section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted complete degree-zero and properness helpers from the already pinned
WIP-compatible TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean and Proper.lean.
The original field restriction is replaced by an arbitrary commutative ring.
This is an independent adaptation at the campaign Mathlib pin; the separate
Tau Ceti package and core pins are not changed.
Design boundary: the actual Proj projective line over a commutative ring,
with its structural morphism proved proper. Named downstream consumer:
constructing the finite integral order-thirteen hyperelliptic map to this
projective line, to establish properness of the actual integral curve.
This file does not assert that the curve morphism has been constructed.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralProjectiveLine
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
universe u

abbrev homogeneousPieces (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

instance (R : Type u) [CommRing R] : GradedAlgebra (homogeneousPieces R) :=
  MvPolynomial.gradedAlgebra

abbrev scheme (R : Type u) [CommRing R] : Scheme.{u} := Proj (homogeneousPieces R)

def degreeZeroRingEquiv (R : Type u) [CommRing R] : R ≃+* homogeneousPieces R 0 :=
  RingEquiv.ofBijective (algebraMap R (homogeneousPieces R 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 2) R (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 2) R) ∈
          (1 : Submodule R (MvPolynomial (Fin 2) R)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

instance (R : Type u) [CommRing R] :
    Algebra.FiniteType (homogeneousPieces R 0) (MvPolynomial (Fin 2) R) := by
  letI : IsScalarTower R (homogeneousPieces R 0) (MvPolynomial (Fin 2) R) :=
    IsScalarTower.of_algebraMap_eq
      (R := R) (S := homogeneousPieces R 0) (A := MvPolynomial (Fin 2) R) (fun r ↦ by rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    R (homogeneousPieces R 0) (MvPolynomial (Fin 2) R)

def structureMap (R : Type u) [CommRing R] : scheme R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (homogeneousPieces R) ≫
    Spec.map (degreeZeroRingEquiv R).toCommRingCatIso.hom

theorem structureMap_isProper (R : Type u) [CommRing R] : IsProper (structureMap R) := by
  dsimp only [structureMap]
  infer_instance

theorem structureMap_locallyOfFiniteType (R : Type u) [CommRing R] :
    LocallyOfFiniteType (structureMap R) := by
  dsimp only [structureMap]
  infer_instance

end MazurTransfer.Order13IntegralProjectiveLine
#print axioms MazurTransfer.Order13IntegralProjectiveLine.degreeZeroRingEquiv
#print axioms MazurTransfer.Order13IntegralProjectiveLine.structureMap_isProper
#print axioms MazurTransfer.Order13IntegralProjectiveLine.structureMap_locallyOfFiniteType

end
end

section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete selected chart presentation proofs adapted from the already pinned
WIP-compatible TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean and Smooth.lean.
All coefficient rings are commutative rings, with no field hypothesis.
The independent campaign-pin adaptation does not change the Tau Ceti package.
Design boundary: polynomial presentations of both actual Proj affine charts
and their joint cover. Named downstream consumer: the finite integral
order-thirteen hyperelliptic map into the actual proper projective line.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralProjectiveLine
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
universe u

@[simp]
theorem coe_degreeZeroRingEquiv_apply (R : Type u) [CommRing R] (r : R) :
    ((degreeZeroRingEquiv R r : homogeneousPieces R 0) : MvPolynomial (Fin 2) R) =
      MvPolynomial.C r := rfl

/-- The standard affine chart `D₊(X₁)` of the projective line. -/
abbrev standardAffineOpen (K : Type u) [CommRing K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))

/-- The affine chart `D₊(X₀)` containing the point at infinity. -/
abbrev infinityAffineOpen (K : Type u) [CommRing K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))

lemma X_one_mem_degree_one (K : Type u) [CommRing K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

lemma X_zero_mem_degree_one (K : Type u) [CommRing K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- The degree-zero homogeneous fraction `X₀ / X₁` on the standard affine chart. -/
@[expose] noncomputable def affineCoordinateAway (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

/-- The regular function `X₀ / X₁` on the standard affine chart `D₊(X₁)`. -/
@[expose] noncomputable def affineCoordinate (K : Type u) [CommRing K] :
  Γ(scheme K, standardAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one).hom (affineCoordinateAway K)

/-- The degree-zero homogeneous fraction `X₁ / X₀` on the affine chart containing
infinity. -/
@[expose] noncomputable def inverseAffineCoordinateAway (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

/-- The regular function `X₁ / X₀` on the affine chart `D₊(X₀)`. -/
@[expose] noncomputable def inverseAffineCoordinate (K : Type u) [CommRing K] :
    Γ(scheme K, infinityAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one).hom (inverseAffineCoordinateAway K)



private lemma adjoin_X_over_degreeZero (K : Type u) [CommRing K] :
    Algebra.adjoin (homogeneousPieces K 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) = ⊤ := by
  apply top_unique
  intro p _
  have hall : ∀ p : MvPolynomial (Fin 2) K,
      p ∈ Algebra.adjoin (homogeneousPieces K 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r =>
        have h := (Algebra.adjoin (homogeneousPieces K 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K))).algebraMap_mem
          (degreeZeroRingEquiv K r)
        simpa using h
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact hall p

/-- The two standard affine charts cover the projective line. -/
lemma standardAffineOpen_sup_infinityAffineOpen_eq_top
    (K : Type u) [CommRing K] :
    standardAffineOpen K ⊔ infinityAffineOpen K = ⊤ := by
  have hcover : ⨆ i : Fin 2,
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero K)
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_right
  · exact le_sup_left




end MazurTransfer.Order13IntegralProjectiveLine

end
end

section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Complete gluing, preimage, finite-morphism and properness proofs adapted
from the pinned WIP-compatible XOneThirteenHyperellipticMap.lean.
The coefficient ring is an arbitrary commutative ring, with no field or
characteristic restriction. No Noetherianity conclusion is asserted for
an arbitrary base ring. The independent adaptation uses the campaign
Mathlib pin and does not alter the core or separate Tau Ceti package pins.
Design boundary: the actual whole integral hyperelliptic map is finite,
and the literal glued order-thirteen curve is proper over its base ring.
Named downstream consumer: the actual smooth proper integral curve family
and its compatible Picard family for torsion specialization.
-/

noncomputable section

namespace MazurTransfer.Order13IntegralHyperellipticMap

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DirectSum
open MazurTransfer MazurTorsion

universe u

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

section ChartRingMaps

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]

/-- Evaluation of the homogeneous coordinates at `[x:1]`. -/
private def standardCoordinatePolynomialHom (x : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 0 then x else 1

private lemma standardCoordinatePolynomialHom_X_one (x : A) :
    standardCoordinatePolynomialHom K A x
        (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [standardCoordinatePolynomialHom]

/-- The standard projective-line chart ring map sending `X₀/X₁` to
`x`. -/
noncomputable def standardChartRingHom (x : A) :
    HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [standardCoordinatePolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

@[simp]
theorem standardChartRingHom_affineCoordinateAway (x : A) :
    standardChartRingHom K A x (Order13IntegralProjectiveLine.affineCoordinateAway K) = x := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    Order13IntegralProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) 1
  simpa [standardCoordinatePolynomialHom] using h

/-- Evaluation of the homogeneous coordinates at `[1:z]`. -/
private def inverseCoordinatePolynomialHom (z : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 1 then z else 1

private lemma inverseCoordinatePolynomialHom_X_zero (z : A) :
    inverseCoordinatePolynomialHom K A z
        (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom]

/-- The infinity projective-line chart ring map sending `X₁/X₀` to
`z`. -/
noncomputable def infinityChartRingHom (z : A) :
    HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (inverseCoordinatePolynomialHom K A z)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

@[simp]
theorem infinityChartRingHom_inverseAffineCoordinateAway (z : A) :
    infinityChartRingHom K A z
        (Order13IntegralProjectiveLine.inverseAffineCoordinateAway K) = z := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    Order13IntegralProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 1
  simpa [inverseCoordinatePolynomialHom] using h

private theorem standardCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardCoordinatePolynomialHom K A x) =
      standardCoordinatePolynomialHom K B (f x) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [standardCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [standardCoordinatePolynomialHom]

private theorem infinityCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (inverseCoordinatePolynomialHom K A z) =
      inverseCoordinatePolynomialHom K B (f z) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [inverseCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [inverseCoordinatePolynomialHom]

/-- Homogeneous evaluation is invariant under the projective rescaling
`[x:1] = [1:z]` when `xz=1`. -/
private theorem eval_standard_eq_pow_mul_eval_inverse
    (p : MvPolynomial (Fin 2) K) (n : ℕ)
    (hp : p.IsHomogeneous n) (x z : A) (hxz : x * z = 1) :
    standardCoordinatePolynomialHom K A x p =
      x ^ n * inverseCoordinatePolynomialHom K A z p := by
  simp only [standardCoordinatePolynomialHom,
    inverseCoordinatePolynomialHom, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using h
  simp only [Fin.prod_univ_two,
    if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_neg (by decide : (0 : Fin 2) ≠ 1), if_true, one_pow,
    one_mul, mul_one]
  rw [← hdeg, pow_add]
  calc
    (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 =
        (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 * 1 := by
          rw [mul_one]
    _ = (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 *
        ((x * z) ^ d 1) := by rw [hxz, one_pow]
    _ = (x ^ d 0 * x ^ d 1) *
        ((algebraMap K A) (MvPolynomial.coeff d p) * z ^ d 1) := by
          rw [mul_pow]
          ring

private theorem overlapDenominator_mem_degree_two :
    MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) ∈
      Order13IntegralProjectiveLine.homogeneousPieces K 2 := by
  simpa using
    (Order13IntegralProjectiveLine.X_one_mem_degree_one K).mul
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K)

/-- Evaluation on the common projective-line chart `D₊(X₁X₀)`,
normalized as `[x:1]` with chosen inverse `z`. -/
private noncomputable def overlapChartRingHom
    (x z : A) (hxz : x * z = 1) :
    HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
      (isUnit_iff_exists_inv.mpr ⟨z, by
        simpa [standardCoordinatePolynomialHom] using hxz⟩)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)))
      (Localization.Away
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))))

private theorem standardChartRingHom_awayMk
    (x : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n) :
    standardChartRingHom K A x
        (HomogeneousLocalization.Away.mk
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_one_mem_degree_one K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) p 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) n
  simpa using h

private theorem infinityChartRingHom_awayMk
    (z : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n) :
    infinityChartRingHom K A z
        (HomogeneousLocalization.Away.mk
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) n p
          (by simpa using hp)) =
      inverseCoordinatePolynomialHom K A z p := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) p 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) n
  simpa using h

private theorem standardChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardChartRingHom K A x) =
      standardChartRingHom K B (f x) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13IntegralProjectiveLine.homogeneousPieces K)
      (Order13IntegralProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    standardChartRingHom_awayMk K A x n p hp',
    standardChartRingHom_awayMk K B (f x) n p hp']
  exact DFunLike.congr_fun
    (standardCoordinatePolynomialHom_naturality K A B f x) p

private theorem infinityChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (infinityChartRingHom K A z) =
      infinityChartRingHom K B (f z) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13IntegralProjectiveLine.homogeneousPieces K)
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    infinityChartRingHom_awayMk K A z n p hp',
    infinityChartRingHom_awayMk K B (f z) n p hp']
  exact DFunLike.congr_fun
    (infinityCoordinatePolynomialHom_naturality K A B f z) p

private theorem overlapChartRingHom_awayMk
    (x z : A) (hxz : x * z = 1) (n : ℕ)
    (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K (n • 2)) :
    overlapChartRingHom K A x z hxz
        (HomogeneousLocalization.Away.mk
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (overlapDenominator_mem_degree_two K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p * z ^ n := by
  simp only [overlapChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
    p z (by simpa [standardCoordinatePolynomialHom] using hxz) n
  simpa using h

private theorem overlapChartRingHom_comp_standardAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) rfl) =
      standardChartRingHom K A x := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13IntegralProjectiveLine.homogeneousPieces K)
      (Order13IntegralProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (0 : Fin 2) ^ n),
    standardChartRingHom_awayMk K A x n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_pos]
    rw [mul_assoc, ← mul_pow, hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K))

private theorem overlapChartRingHom_comp_infinityAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_one_mem_degree_one K)
          (mul_comm _ _)) =
      infinityChartRingHom K A z := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (Order13IntegralProjectiveLine.homogeneousPieces K)
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ Order13IntegralProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (1 : Fin 2) ^ n),
    infinityChartRingHom_awayMk K A z n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), one_pow,
      mul_one]
    change standardCoordinatePolynomialHom K A x p * z ^ n =
      inverseCoordinatePolynomialHom K A z p
    rw [eval_standard_eq_pow_mul_eval_inverse K A p n hp' x z hxz]
    calc
      (x ^ n * inverseCoordinatePolynomialHom K A z p) * z ^ n =
          inverseCoordinatePolynomialHom K A z p * (x * z) ^ n := by
            rw [mul_pow]
            ring
      _ = inverseCoordinatePolynomialHom K A z p := by
        rw [hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K))

end ChartRingMaps

section ChartFiniteness

variable (K : Type u) [CommRing K]

private noncomputable def standardPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)))).comp
      (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (Order13IntegralProjectiveLine.affineCoordinateAway K)

private theorem standardChartRingHom_comp_standardPolynomialToAway :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).comp
        (standardPolynomialToAway K) =
      (AdjoinRoot.of
        (XOneThirteenAffineCurve.affineEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show standardPolynomialToAway K (Polynomial.C k) =
        (algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        Order13IntegralProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_one_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((Order13IntegralProjectiveLine.degreeZeroRingEquiv K k :
            Order13IntegralProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [Order13IntegralProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      standardChartRingHom_awayMk K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show standardCoordinatePolynomialHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) (MvPolynomial.C k) =
      algebraMap K (XOneThirteenAffineCurve.CoordinateRing K) k by
        simp [standardCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenAffineCurve.CoordinateRing K) k)
  · simp [standardPolynomialToAway,
      XOneThirteenAffineCurve.xCoordinate]

private theorem affineEquation_monic :
    (XOneThirteenAffineCurve.affineEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The standard chart of the hyperelliptic map is finite. -/
theorem standardChartRingHom_finite :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := standardPolynomialToAway K)
  rw [standardChartRingHom_comp_standardPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot (XOneThirteenAffineCurve.affineEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (affineEquation_monic K |>.finite_adjoinRoot)

private noncomputable def infinityPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2)))).comp
      (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (Order13IntegralProjectiveLine.inverseAffineCoordinateAway K)

private theorem infinityChartRingHom_comp_infinityPolynomialToAway :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).comp
        (infinityPolynomialToAway K) =
      (AdjoinRoot.of
        (XOneThirteenProjectiveCurve.reciprocalEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show infinityPolynomialToAway K (Polynomial.C k) =
        (algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        Order13IntegralProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (Order13IntegralProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (Order13IntegralProjectiveLine.homogeneousPieces K)
          (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((Order13IntegralProjectiveLine.degreeZeroRingEquiv K k :
            Order13IntegralProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [Order13IntegralProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      infinityChartRingHom_awayMk K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show inverseCoordinatePolynomialHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K)
        (MvPolynomial.C k) =
      algebraMap K (XOneThirteenProjectiveCurve.ReciprocalRing K) k by
        simp [inverseCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenProjectiveCurve.ReciprocalRing K) k)
  · simp [infinityPolynomialToAway,
      XOneThirteenProjectiveCurve.zCoordinate]

private theorem reciprocalEquation_monic :
    (XOneThirteenProjectiveCurve.reciprocalEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The infinity chart of the hyperelliptic map is finite. -/
theorem infinityChartRingHom_finite :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := infinityPolynomialToAway K)
  rw [infinityChartRingHom_comp_infinityPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot
      (XOneThirteenProjectiveCurve.reciprocalEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (reciprocalEquation_monic K |>.finite_adjoinRoot)

end ChartFiniteness

section ChartMorphisms

variable (K : Type u) [CommRing K]

private theorem projectiveLine_chart_maps_eq
    (A : Type u) [CommRing A] [Algebra K A]
    (x z : A) (hxz : x * z = 1) :
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
        Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one =
      Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one := by
  let H := Order13IntegralProjectiveLine.homogeneousPieces K
  let X₀ : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let X₁ : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let q : MvPolynomial (Fin 2) K := X₁ * X₀
  let hq : q ∈ H 2 := overlapDenominator_mem_degree_two K
  have hstd := overlapChartRingHom_comp_standardAwayMap K A x z hxz
  have hinf := overlapChartRingHom_comp_infinityAwayMap K A x z hxz
  calc
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
          Proj.awayι H X₁ (Order13IntegralProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one =
        (Spec.map (CommRingCat.ofHom (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₁) (x := q)
              (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) rfl))) ≫
          Proj.awayι H X₁ (Order13IntegralProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one := by
              rw [← Spec.map_comp]
              congr 2
              apply CommRingCat.hom_ext
              exact hstd.symm
    _ = Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
        Proj.awayι H q hq (by omega) := by
          rw [Category.assoc,
            Proj.SpecMap_awayMap_awayι
              (f := X₁) (g := X₀) (x := q) H
              (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one
              (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) rfl]
    _ = (Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₀) (x := q)
              (Order13IntegralProjectiveLine.X_one_mem_degree_one K)
              (mul_comm X₁ X₀)))) ≫
        Proj.awayι H X₀ (Order13IntegralProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [Category.assoc,
              Proj.SpecMap_awayMap_awayι
                (f := X₀) (g := X₁) (x := q) H
                (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one
                (Order13IntegralProjectiveLine.X_one_mem_degree_one K) (mul_comm X₁ X₀)]
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι H X₀ (Order13IntegralProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hinf

/-- The ordinary hyperelliptic chart map, with projective coordinate
`[x:1]`. -/
noncomputable def ordinaryChartToProjectiveLine :
    XOneThirteenAffineCurve.scheme K ⟶ Order13IntegralProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
    Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one

/-- The reciprocal hyperelliptic chart map, with projective coordinate
`[1:z]`. -/
noncomputable def reciprocalChartToProjectiveLine :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      Order13IntegralProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
    Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one

private theorem ordinaryChartToProjectiveLine_toSpecZero :
    ordinaryChartToProjectiveLine K ≫
        Proj.toSpecZero (Order13IntegralProjectiveLine.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K (XOneThirteenAffineCurve.CoordinateRing K)).comp
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [ordinaryChartToProjectiveLine, Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (Order13IntegralProjectiveLine.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2)))
        (Order13IntegralProjectiveLine.degreeZeroRingEquiv K r)) =
    algebraMap K (XOneThirteenAffineCurve.CoordinateRing K) r
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K))
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) 0
  convert h using 1
  · congr 1
  · simp [standardCoordinatePolynomialHom]

private theorem reciprocalChartToProjectiveLine_toSpecZero :
    reciprocalChartToProjectiveLine K ≫
        Proj.toSpecZero (Order13IntegralProjectiveLine.homogeneousPieces K) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap K
            (XOneThirteenProjectiveCurve.ReciprocalRing K)).comp
          (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).symm.toRingHom)) := by
  rw [reciprocalChartToProjectiveLine, Category.assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  ext p
  obtain ⟨r, rfl⟩ := (Order13IntegralProjectiveLine.degreeZeroRingEquiv K).surjective p
  simp only [CommRingCat.ofHom_comp, CommRingCat.hom_comp,
    ConcreteCategory.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  change infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)
      (HomogeneousLocalization.fromZeroRingHom
        (Order13IntegralProjectiveLine.homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))
        (Order13IntegralProjectiveLine.degreeZeroRingEquiv K r)) =
    algebraMap K (XOneThirteenProjectiveCurve.ReciprocalRing K) r
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K))
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C r) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 0
  convert h using 1
  · congr 1
  · simp [inverseCoordinatePolynomialHom]

@[simp, reassoc]
theorem ordinaryChartToProjectiveLine_structureMap :
    ordinaryChartToProjectiveLine K ≫ Order13IntegralProjectiveLine.structureMap K =
      XOneThirteenProjectiveCurve.ordinaryChartToBase K := by
  rw [Order13IntegralProjectiveLine.structureMap, ← Category.assoc,
    ordinaryChartToProjectiveLine_toSpecZero, ← Spec.map_comp]
  unfold XOneThirteenProjectiveCurve.ordinaryChartToBase
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

@[simp, reassoc]
theorem reciprocalChartToProjectiveLine_structureMap :
    reciprocalChartToProjectiveLine K ≫ Order13IntegralProjectiveLine.structureMap K =
      XOneThirteenProjectiveCurve.reciprocalChartToBase K := by
  rw [Order13IntegralProjectiveLine.structureMap, ← Category.assoc,
    reciprocalChartToProjectiveLine_toSpecZero, ← Spec.map_comp]
  unfold XOneThirteenProjectiveCurve.reciprocalChartToBase
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  ext r
  simp

theorem ordinaryChartToProjectiveLine_preimage_standardAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.standardAffineOpen K = ⊤ := by
  rw [show Order13IntegralProjectiveLine.standardAffineOpen K =
      (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one).symm]
  unfold ordinaryChartToProjectiveLine XOneThirteenAffineCurve.scheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem inverseAffineCoordinateAway_eq_isLocalizationElem :
    Order13IntegralProjectiveLine.inverseAffineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K)
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K) := by
  simp [Order13IntegralProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.standardAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  unfold reciprocalChartToProjectiveLine
    XOneThirteenProjectiveCurve.reciprocalScheme
  change (Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
      Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (Order13IntegralProjectiveLine.homogeneousPieces K)
    (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one
    (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← inverseAffineCoordinateAway_eq_isLocalizationElem K]
  exact infinityChartRingHom_inverseAffineCoordinateAway K
    (XOneThirteenProjectiveCurve.ReciprocalRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

theorem reciprocalChartToProjectiveLine_preimage_infinityAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.infinityAffineOpen K = ⊤ := by
  rw [show Order13IntegralProjectiveLine.infinityAffineOpen K =
      (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).symm]
  unfold reciprocalChartToProjectiveLine
    XOneThirteenProjectiveCurve.reciprocalScheme
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem affineCoordinateAway_eq_isLocalizationElem :
    Order13IntegralProjectiveLine.affineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K)
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) := by
  simp [Order13IntegralProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.infinityAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenAffineCurve.xCoordinate K) := by
  unfold ordinaryChartToProjectiveLine
  change (Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
      Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (Order13IntegralProjectiveLine.homogeneousPieces K)
    (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one
    (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← affineCoordinateAway_eq_isLocalizationElem K]
  exact standardChartRingHom_affineCoordinateAway K
    (XOneThirteenAffineCurve.CoordinateRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private theorem ordinaryReciprocalOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K))) := by
  rfl

private theorem reciprocalOrdinaryOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenProjectiveCurve.ReciprocalRing K)
          (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K))) := by
  rfl

private theorem ordinaryReciprocalOverlapTransition_eq :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom := by
  rfl

private theorem reciprocalOrdinaryOverlapTransition_eq :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        reciprocalOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.standardAffineOpen K =
      reciprocalOverlapOpen K := by
  exact reciprocalChartToProjectiveLine_preimage_standardAffineOpen K

private theorem reciprocalGlueOverlap_opensRange :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg reciprocal_ne_ordinary]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage :
    reciprocalOverlapOpen K =
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm

/-- On the reciprocal chart, the overlap with the ordinary chart is exactly
the principal open where the reciprocal coordinate `z` is nonzero. -/
@[simp]
theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage K).symm

private instance ordinaryOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        ordinary_ne_reciprocal) := by
  rw [ordinaryReciprocalOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenAffineCurve.xCoordinate K)

private noncomputable abbrev ordinaryOverlapOpen :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenAffineCurve.xCoordinate K)

private theorem ordinaryOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      ordinary_ne_reciprocal).opensRange =
        ordinaryOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private instance ordinaryGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        Order13IntegralProjectiveLine.infinityAffineOpen K =
      ordinaryOverlapOpen K := by
  exact ordinaryChartToProjectiveLine_preimage_infinityAffineOpen K

private theorem ordinaryGlueOverlap_opensRange :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      ordinaryOverlapOpen K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg ordinary_ne_reciprocal]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact ordinaryOverlapInclusion_opensRange K

private theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.ordinaryChartMap K q ∈
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem ordinaryOverlapOpen_eq_chartMap_preimage :
    ordinaryOverlapOpen K =
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange :=
  (ordinaryGlueOverlap_opensRange K).symm.trans
    (ordinaryChartMap_preimage_reciprocalChartMap_opensRange K).symm

/-- On the ordinary chart, the overlap with the reciprocal chart is exactly
the principal open where `x` is nonzero. -/
@[simp]
theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenAffineCurve.xCoordinate K) := by
  exact (ordinaryOverlapOpen_eq_chartMap_preimage K).symm

private theorem ordinary_reciprocal_hyperelliptic_compatible :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let B := XOneThirteenProjectiveCurve.ReciprocalRing K
  let LA := XOneThirteenProjectiveCurve.OrdinaryOverlapRing K
  let LB := XOneThirteenProjectiveCurve.ReciprocalOverlapRing K
  let x : LA := algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)
  let z : LA := IsLocalization.Away.invSelf
    (XOneThirteenAffineCurve.xCoordinate K)
  let ordinaryLocalization : A →ₐ[K] LA :=
    IsScalarTower.toAlgHom K A LA
  let reciprocalToOrdinary : B →ₐ[K] LA :=
    (XOneThirteenProjectiveCurve.reciprocalToOrdinary K).comp
      (IsScalarTower.toAlgHom K B LB)
  have hxz : x * z = 1 := by
    exact IsLocalization.Away.mul_invSelf
      (XOneThirteenAffineCurve.xCoordinate K)
  have hz : reciprocalToOrdinary
      (XOneThirteenProjectiveCurve.zCoordinate K) = z := by
    change XOneThirteenProjectiveCurve.reciprocalToOrdinary K
      (algebraMap B LB (XOneThirteenProjectiveCurve.zCoordinate K)) = z
    rw [XOneThirteenProjectiveCurve.reciprocalToOrdinary_algebraMap,
      XOneThirteenProjectiveCurve.reciprocalToOrdinaryBase_z]
    rfl
  have hordinary := standardChartRingHom_naturality K A LA
    ordinaryLocalization (XOneThirteenAffineCurve.xCoordinate K)
  have hreciprocal := infinityChartRingHom_naturality K B LA
    reciprocalToOrdinary (XOneThirteenProjectiveCurve.zCoordinate K)
  rw [hz] at hreciprocal
  calc
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
        Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one := by
      rw [ordinaryReciprocalOverlapInclusion_eq]
      unfold ordinaryChartToProjectiveLine XOneThirteenAffineCurve.scheme
      change Spec.map (CommRingCat.ofHom (algebraMap A LA)) ≫
          (Spec.map (CommRingCat.ofHom
            (standardChartRingHom K A
              (XOneThirteenAffineCurve.xCoordinate K))) ≫
            Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
              (MvPolynomial.X (1 : Fin 2))
              (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one) =
        Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
          Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hordinary
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
        Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one :=
      projectiveLine_chart_maps_eq K LA x z hxz
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
      rw [ordinaryReciprocalOverlapTransition_eq,
        XOneThirteenProjectiveCurve.overlapSchemeIso_hom,
        reciprocalOrdinaryOverlapInclusion_eq]
      unfold reciprocalChartToProjectiveLine
        XOneThirteenProjectiveCurve.reciprocalScheme
      change Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
          Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one =
        Spec.map (CommRingCat.ofHom
          (XOneThirteenProjectiveCurve.reciprocalToOrdinary K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B LB)) ≫
          (Spec.map (CommRingCat.ofHom
            (infinityChartRingHom K B
              (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
            Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
              (MvPolynomial.X (0 : Fin 2))
              (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one)
      symm
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hreciprocal

private theorem reciprocal_ordinary_hyperelliptic_compatible :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
  let l := XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
    reciprocalChartToProjectiveLine K
  calc
    l = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom ≫ l := by
      rw [(XOneThirteenProjectiveCurve.overlapSchemeIso K).inv_hom_id_assoc]
    _ = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rw [ordinary_reciprocal_hyperelliptic_compatible K]
      rfl
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rw [reciprocalOrdinaryOverlapTransition_eq]

/-- The chartwise hyperelliptic maps before descent through the gluing. -/
noncomputable def chartToProjectiveLine :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      XOneThirteenProjectiveCurve.chartScheme K i ⟶
        Order13IntegralProjectiveLine.scheme K
  | .ordinary => ordinaryChartToProjectiveLine K
  | .reciprocal => reciprocalChartToProjectiveLine K

/-- The hyperelliptic map descended from the two checked chart maps. -/
noncomputable def gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.curveScheme K ⟶
      Order13IntegralProjectiveLine.scheme K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  exact Limits.Multicoequalizer.desc
    (XOneThirteenProjectiveCurve.glueData K).toGlueData.diagram
    (Order13IntegralProjectiveLine.scheme K) (chartToProjectiveLine K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact ordinary_reciprocal_hyperelliptic_compatible K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact reciprocal_ordinary_hyperelliptic_compatible K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
        gluedHyperellipticMap K =
      ordinaryChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.ordinaryChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
        gluedHyperellipticMap K =
      reciprocalChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.reciprocalChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

theorem gluedHyperellipticMap_preimage_standardAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        Order13IntegralProjectiveLine.standardAffineOpen K =
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13IntegralProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ⊤ := ordinaryChartToProjectiveLine_preimage_standardAffineOpen K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13IntegralProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            Order13IntegralProjectiveLine.standardAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = reciprocalOverlapOpen K :=
        reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapOpen K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
        reciprocalOverlapOpen_eq_chartMap_preimage K
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

theorem gluedHyperellipticMap_preimage_infinityAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        Order13IntegralProjectiveLine.infinityAffineOpen K =
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13IntegralProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ordinaryOverlapOpen K :=
        ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapOpen K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange :=
        ordinaryOverlapOpen_eq_chartMap_preimage K
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              Order13IntegralProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            Order13IntegralProjectiveLine.infinityAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = ⊤ := reciprocalChartToProjectiveLine_preimage_infinityAffineOpen K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

private noncomputable abbrev projectiveLineChartScheme :
    XOneThirteenProjectiveCurve.Chart.{u} → Scheme
  | .ordinary => Spec (.of <|
      HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
  | .reciprocal => Spec (.of <|
      HomogeneousLocalization.Away (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))

private noncomputable def projectiveLineChartMap :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      projectiveLineChartScheme K i ⟶ Order13IntegralProjectiveLine.scheme K
  | .ordinary => Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one
  | .reciprocal => Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one

private instance projectiveLineChartMap_isOpenImmersion
    (i : XOneThirteenProjectiveCurve.Chart.{u}) :
    IsOpenImmersion (projectiveLineChartMap K i) := by
  rcases i with (_ | _)
  · change IsOpenImmersion
      (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one)
    infer_instance
  · change IsOpenImmersion
      (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one)
    infer_instance

private theorem projectiveLineChartMap_ordinary_opensRange :
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      Order13IntegralProjectiveLine.standardAffineOpen K := by
  exact Proj.opensRange_awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
    (MvPolynomial.X (1 : Fin 2))
    (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one

private theorem projectiveLineChartMap_reciprocal_opensRange :
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      Order13IntegralProjectiveLine.infinityAffineOpen K := by
  exact Proj.opensRange_awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
    (MvPolynomial.X (0 : Fin 2))
    (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one

private noncomputable def projectiveLineChartCover :
    (Order13IntegralProjectiveLine.scheme K).OpenCover where
  I₀ := XOneThirteenProjectiveCurve.Chart.{u}
  X := projectiveLineChartScheme K
  f := projectiveLineChartMap K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp : p ∈ Order13IntegralProjectiveLine.standardAffineOpen K ⊔
          Order13IntegralProjectiveLine.infinityAffineOpen K := by
        rw [Order13IntegralProjectiveLine.standardAffineOpen_sup_infinityAffineOpen_eq_top]
        trivial
      change p ∈ (Order13IntegralProjectiveLine.standardAffineOpen K :
          Set (Order13IntegralProjectiveLine.scheme K)) ∪
        (Order13IntegralProjectiveLine.infinityAffineOpen K :
          Set (Order13IntegralProjectiveLine.scheme K)) at hp
      rcases hp with hp | hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.ordinary, ?_⟩
        change p ∈ (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (Order13IntegralProjectiveLine.X_one_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.reciprocal, ?_⟩
        change p ∈ (Proj.awayι (Order13IntegralProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (Order13IntegralProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
    · intro i
      exact projectiveLineChartMap_isOpenImmersion K i

private noncomputable def ordinaryChartFiniteMap :
    XOneThirteenAffineCurve.scheme K ⟶
      projectiveLineChartScheme K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)))

private noncomputable def reciprocalChartFiniteMap :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      projectiveLineChartScheme K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)))

private theorem ordinaryChartSquare_isPullback :
    IsPullback (ordinaryChartFiniteMap K)
      (XOneThirteenProjectiveCurve.ordinaryChartMap K)
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [ordinaryChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_ordinary_opensRange]
    exact gluedHyperellipticMap_preimage_standardAffineOpen K

private theorem reciprocalChartSquare_isPullback :
    IsPullback (reciprocalChartFiniteMap K)
      (XOneThirteenProjectiveCurve.reciprocalChartMap K)
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
    projectiveLineChartMap_isOpenImmersion K _
  apply IsOpenImmersion.isPullback
  · rw [reciprocalChartMap_gluedHyperellipticMap]
    rfl
  · rw [projectiveLineChartMap_reciprocal_opensRange]
    exact gluedHyperellipticMap_preimage_infinityAffineOpen K

/-- The morphism property underlying `IsFinite`, named explicitly so that
Mathlib's affine-local framework can elaborate it at the default transparency
setting. -/
private abbrev finiteMorphismProperty : MorphismProperty Scheme :=
  fun {_ _} f => IsFinite f

private instance finiteMorphismProperty_hasAffineProperty :
    HasAffineProperty finiteMorphismProperty (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away
    RingHom.finite_ofLocalizationSpan]
  simp [finiteMorphismProperty, isFinite_iff]

private theorem ordinaryCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := ordinaryChartSquare_isPullback K
  change finiteMorphismProperty (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact standardChartRingHom_finite K

private theorem reciprocalCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := reciprocalChartSquare_isPullback K
  change finiteMorphismProperty (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := finiteMorphismProperty) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact infinityChartRingHom_finite K

noncomputable instance gluedHyperellipticMap_isFinite :
    IsFinite (gluedHyperellipticMap K) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (P := finiteMorphismProperty) (projectiveLineChartCover K)
  intro i
  rcases i with (_ | _)
  · exact ordinaryCoverPullbackHom_isFinite K
  · exact reciprocalCoverPullbackHom_isFinite K

end ChartMorphisms

end MazurTransfer.Order13IntegralHyperellipticMap

namespace MazurTransfer.Order13IntegralProperCurve
open MazurTorsion.XOneThirteenProjectiveCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open MazurTransfer MazurTorsion

universe u

variable (K : Type u) [CommRing K]

/-- The degree-two coordinate map from the glued order-thirteen curve to
Tau Ceti's concrete projective line. -/
noncomputable def hyperellipticMap :
    curveScheme K ⟶ Order13IntegralProjectiveLine.scheme K :=
  MazurTransfer.Order13IntegralHyperellipticMap.gluedHyperellipticMap K

@[simp, reassoc]
theorem ordinaryChartMap_hyperellipticMap :
    ordinaryChartMap K ≫ hyperellipticMap K =
      MazurTransfer.Order13IntegralHyperellipticMap.ordinaryChartToProjectiveLine K := by
  exact MazurTransfer.Order13IntegralHyperellipticMap.ordinaryChartMap_gluedHyperellipticMap K

@[simp, reassoc]
theorem reciprocalChartMap_hyperellipticMap :
    reciprocalChartMap K ≫ hyperellipticMap K =
      MazurTransfer.Order13IntegralHyperellipticMap.reciprocalChartToProjectiveLine K := by
  exact MazurTransfer.Order13IntegralHyperellipticMap.reciprocalChartMap_gluedHyperellipticMap K

@[simp]
theorem hyperellipticMap_preimage_standardAffineOpen :
    hyperellipticMap K ⁻¹ᵁ Order13IntegralProjectiveLine.standardAffineOpen K =
      (ordinaryChartMap K).opensRange :=
  MazurTransfer.Order13IntegralHyperellipticMap.gluedHyperellipticMap_preimage_standardAffineOpen K

@[simp]
theorem hyperellipticMap_preimage_infinityAffineOpen :
    hyperellipticMap K ⁻¹ᵁ Order13IntegralProjectiveLine.infinityAffineOpen K =
      (reciprocalChartMap K).opensRange :=
  MazurTransfer.Order13IntegralHyperellipticMap.gluedHyperellipticMap_preimage_infinityAffineOpen K

noncomputable instance hyperellipticMap_isFinite :
    IsFinite (hyperellipticMap K) :=
  MazurTransfer.Order13IntegralHyperellipticMap.gluedHyperellipticMap_isFinite K

/-- The structure morphism obtained by gluing the affine algebra maps is the
finite hyperelliptic map followed by the structure morphism of projective
line. -/
theorem curveToBase_eq_hyperellipticMap_comp_structureMap :
    curveToBase K =
      hyperellipticMap K ≫ Order13IntegralProjectiveLine.structureMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  apply Limits.Multicoequalizer.hom_ext
  intro i
  rcases i with (_ | _)
  · change ordinaryChartMap K ≫ curveToBase K =
      ordinaryChartMap K ≫ hyperellipticMap K ≫
        Order13IntegralProjectiveLine.structureMap K
    rw [ordinaryChartMap_curveToBase,
      ordinaryChartMap_hyperellipticMap_assoc,
      MazurTransfer.Order13IntegralHyperellipticMap.ordinaryChartToProjectiveLine_structureMap]
  · change reciprocalChartMap K ≫ curveToBase K =
      reciprocalChartMap K ≫ hyperellipticMap K ≫
        Order13IntegralProjectiveLine.structureMap K
    rw [reciprocalChartMap_curveToBase,
      reciprocalChartMap_hyperellipticMap_assoc,
      MazurTransfer.Order13IntegralHyperellipticMap.reciprocalChartToProjectiveLine_structureMap]

/-- The actual glued order-thirteen curve is proper over its coefficient
ring.  This is the first downstream consumer of the structural-morphism
comparison above. -/
theorem curveToBase_isProper : IsProper (curveToBase K) := by
  letI : IsProper (Order13IntegralProjectiveLine.structureMap K) :=
    Order13IntegralProjectiveLine.structureMap_isProper K
  rw [curveToBase_eq_hyperellipticMap_comp_structureMap]
  infer_instance


end MazurTransfer.Order13IntegralProperCurve
#print axioms MazurTransfer.Order13IntegralHyperellipticMap.gluedHyperellipticMap_isFinite
#print axioms MazurTransfer.Order13IntegralProperCurve.curveToBase_eq_hyperellipticMap_comp_structureMap
#print axioms MazurTransfer.Order13IntegralProperCurve.curveToBase_isProper

end
end

open AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem solution.{u}
    (R : Type u) [CommRing R] :
    IsProper (curveToBase R) := by
  exact MazurTransfer.Order13IntegralProperCurve.curveToBase_isProper R

#print axioms solution
