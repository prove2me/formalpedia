-- Prove2me | solution 1 for InverseGalois.generic_inverse_galois_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T20:29:54.11816+00:00
-- url     : https://prove2.me/submissions/3f77459d-cd9a-4797-a413-8587e1adbe80

import Mathlib
import Definitions.Def_InverseGalois_realizability
import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_mvPolynomial_faithfulSMul

open MvPolynomial InverseGalois

noncomputable section

namespace GenericSymmetric

universe u v

/-- Realizability of `G` over `K` from an abstract Galois-group action on `L/K`. -/
theorem isRealizable_of_isGaloisGroup (G : Type v) [Group G] [Finite G] (K L : Type u)
    [Field K] [Field L] [Algebra K L] [MulSemiringAction G L] [IsGaloisGroup G K L] :
    IsRealizable K G := by
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).mpr (algebraMap K L).injective
  exact ⟨⟨{ L := L
            to_field := inferInstance
            to_algebra := inferInstance
            to_isGalois := IsGaloisGroup.isGalois G K L
            iso := IsGaloisGroup.mulEquivAlgEquiv G K L }⟩⟩

/-- Transport realizability along a group isomorphism. -/
theorem IsRealizable.congr {K : Type u} [Field K] {G : Type v} {G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (h : IsRealizable K G) : IsRealizable K G' := by
  obtain ⟨r⟩ := h.exists_realization
  exact ⟨⟨{ L := r.L
            to_field := r.to_field
            to_algebra := r.to_algebra
            to_isGalois := r.to_isGalois
            iso := e.symm.trans r.iso }⟩⟩

section Symmetric

variable (S : Type) [Fintype S]

local instance actPoly : MulSemiringAction (Equiv.Perm S) (MvPolynomial S ℚ) :=
  mvPolynomialMulSemiringAction (Equiv.Perm S) S ℚ

local instance faithPoly : FaithfulSMul (Equiv.Perm S) (MvPolynomial S ℚ) :=
  mvPolynomial_faithfulSMul (Equiv.Perm S) S ℚ

local instance actFrac :
    MulSemiringAction (Equiv.Perm S) (FractionRing (MvPolynomial S ℚ)) :=
  IsFractionRing.mulSemiringAction _ (MvPolynomial S ℚ) _

local instance distribFrac :
    SMulDistribClass (Equiv.Perm S) (MvPolynomial S ℚ)
      (FractionRing (MvPolynomial S ℚ)) :=
  IsFractionRing.smulDistribClass _ (MvPolynomial S ℚ) _

local instance faithFrac :
    FaithfulSMul (Equiv.Perm S) (FractionRing (MvPolynomial S ℚ)) :=
  IsFractionRing.faithfulSMul _ (MvPolynomial S ℚ) _

/-- The action on polynomials is the renaming action. -/
theorem smul_poly_eq (g : Equiv.Perm S) (p : MvPolynomial S ℚ) :
    g • p = rename g p := rfl

/-- `algebraMap` into the fraction field is equivariant. -/
theorem algebraMap_smul_eq (g : Equiv.Perm S) (p : MvPolynomial S ℚ) :
    algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) (g • p)
      = g • algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) p := by
  have h1 : ∀ q : MvPolynomial S ℚ,
      algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) q
        = q • (1 : FractionRing (MvPolynomial S ℚ)) := by
    intro q; rw [Algebra.smul_def, mul_one]
  rw [h1, h1, SMulDistribClass.smul_distrib_smul, smul_one]


/-- The `i`-th elementary symmetric polynomial (`i = 1, …, n`), viewed inside the
rational function field. -/
def esymmGen (i : Fin (Fintype.card S)) : FractionRing (MvPolynomial S ℚ) :=
  algebraMap (MvPolynomial S ℚ) _ (esymm S ℚ ((i : ℕ) + 1))

/-- The elementary symmetric polynomials `e₁, …, eₙ` are algebraically independent over `ℚ`. -/
theorem algInd_esymmGen : AlgebraicIndependent ℚ (esymmGen S) := by
  have h0 : Function.Injective (esymmAlgHom S ℚ (Fintype.card S)) :=
    esymmAlgHom_injective ℚ le_rfl
  have h1 : AlgebraicIndependent ℚ
      (fun i : Fin (Fintype.card S) =>
        (⟨esymm S ℚ ((i : ℕ) + 1), esymm_isSymmetric S ℚ _⟩ :
          symmetricSubalgebra S ℚ)) :=
    algebraicIndependent_iff_injective_aeval.mpr h0
  have h2 := h1.map (f := (symmetricSubalgebra S ℚ).val)
    (Set.injOn_of_injective Subtype.val_injective)
  have h3 := h2.map
    (f := IsScalarTower.toAlgHom ℚ (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)))
    (Set.injOn_of_injective (IsFractionRing.injective _ _))
  exact h3

/-- The invariants of the `Sym(S)`-action, as an intermediate field over `ℚ`. -/
def fixedIF : IntermediateField ℚ (FractionRing (MvPolynomial S ℚ)) :=
  (FixedPoints.subfield (Equiv.Perm S)
      (FractionRing (MvPolynomial S ℚ))).toIntermediateField (by
    intro q g
    rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial S ℚ)
      (FractionRing (MvPolynomial S ℚ)) q, ← algebraMap_smul_eq, smul_poly_eq]
    simp [MvPolynomial.algebraMap_eq])

theorem mem_fixedIF {x : FractionRing (MvPolynomial S ℚ)} :
    x ∈ fixedIF S ↔ ∀ g : Equiv.Perm S, g • x = x := Iff.rfl

theorem esymmGen_mem_fixedIF (i : Fin (Fintype.card S)) : esymmGen S i ∈ fixedIF S := by
  intro g
  rw [esymmGen, ← algebraMap_smul_eq, smul_poly_eq]
  congr 1
  exact esymm_isSymmetric S ℚ _ g


/-- The ring map sending the `i`-th variable to the elementary symmetric polynomial `e_{i+1}`,
landing in the rational function field `ℚ(x_s : s ∈ S)`. -/
def coeffHom :
    MvPolynomial (Fin (Fintype.card S)) ℚ →+* FractionRing (MvPolynomial S ℚ) :=
  (algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ))).comp
    (aeval (fun i : Fin (Fintype.card S) => esymm S ℚ ((i : ℕ) + 1)) :
      MvPolynomial (Fin (Fintype.card S)) ℚ →ₐ[ℚ] MvPolynomial S ℚ).toRingHom

theorem coeffHom_apply (u : MvPolynomial (Fin (Fintype.card S)) ℚ) :
    coeffHom S u = algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ))
      (aeval (fun i : Fin (Fintype.card S) => esymm S ℚ ((i : ℕ) + 1)) u) := rfl

/-- `e₁, …, eₙ` are algebraically independent: `coeffHom` is injective. -/
theorem coeffHom_injective : Function.Injective (coeffHom S) := by
  have h0 : Function.Injective (esymmAlgHom S ℚ (Fintype.card S)) :=
    esymmAlgHom_injective ℚ le_rfl
  have h1 : Function.Injective
      (aeval (fun i : Fin (Fintype.card S) => esymm S ℚ ((i : ℕ) + 1)) :
        MvPolynomial (Fin (Fintype.card S)) ℚ → MvPolynomial S ℚ) := by
    intro u v huv
    refine h0 (Subtype.ext ?_)
    rw [esymmAlgHom_apply, esymmAlgHom_apply]
    exact huv
  intro u v huv
  exact h1 (IsFractionRing.injective (MvPolynomial S ℚ)
    (FractionRing (MvPolynomial S ℚ)) huv)

/-- The image of `coeffHom` consists of symmetric functions. -/
theorem smul_coeffHom (g : Equiv.Perm S) (u : MvPolynomial (Fin (Fintype.card S)) ℚ) :
    g • coeffHom S u = coeffHom S u := by
  have hhom : (MulSemiringAction.toRingHom (Equiv.Perm S)
      (FractionRing (MvPolynomial S ℚ)) g).comp (coeffHom S) = coeffHom S := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show g • coeffHom S (C r) = coeffHom S (C r)
      rw [coeffHom_apply, aeval_C, ← algebraMap_smul_eq, smul_poly_eq]
      simp [MvPolynomial.algebraMap_eq]
    · intro i
      show g • coeffHom S (X i) = coeffHom S (X i)
      rw [coeffHom_apply, aeval_X, ← algebraMap_smul_eq, smul_poly_eq]
      congr 1
      exact esymm_isSymmetric S ℚ _ g
  exact RingHom.congr_fun hhom u

/-- Every symmetric polynomial is a polynomial in `e₁, …, eₙ`
(the fundamental theorem of symmetric polynomials). -/
theorem exists_coeffHom_of_isSymmetric {p : MvPolynomial S ℚ} (hp : p.IsSymmetric) :
    ∃ u, coeffHom S u
      = algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) p := by
  obtain ⟨u, hu⟩ := esymmAlgHom_surjective ℚ (le_refl (Fintype.card S)) ⟨p, hp⟩
  refine ⟨u, ?_⟩
  have h : (aeval (fun i : Fin (Fintype.card S) => esymm S ℚ ((i : ℕ) + 1)) u) = p := by
    rw [← esymmAlgHom_apply, hu]
  rw [coeffHom_apply, h]

/-- The embedding of the rational function field in the coefficients `e₁, …, eₙ`. -/
def coeffEmb : FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ) →+*
    FractionRing (MvPolynomial S ℚ) :=
  IsFractionRing.lift (coeffHom_injective S)

theorem coeffEmb_algebraMap (u : MvPolynomial (Fin (Fintype.card S)) ℚ) :
    coeffEmb S (algebraMap _ _ u) = coeffHom S u :=
  IsFractionRing.lift_algebraMap (coeffHom_injective S) u

theorem smul_coeffEmb (g : Equiv.Perm S)
    (z : FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ)) :
    g • coeffEmb S z = coeffEmb S z := by
  obtain ⟨a, b, _, hab⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin (Fintype.card S)) ℚ) z
  rw [← hab, map_div₀,
    show g • (coeffEmb S (algebraMap _ _ a) / coeffEmb S (algebraMap _ _ b))
      = (g • coeffEmb S (algebraMap _ _ a)) / (g • coeffEmb S (algebraMap _ _ b)) from
      map_div₀ (MulSemiringAction.toRingHom (Equiv.Perm S)
        (FractionRing (MvPolynomial S ℚ)) g) _ _,
    coeffEmb_algebraMap, coeffEmb_algebraMap, smul_coeffHom, smul_coeffHom]

local instance algCoeff : Algebra (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ))
    (FractionRing (MvPolynomial S ℚ)) := (coeffEmb S).toAlgebra

theorem algebraMap_coeff_eq
    (z : FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ)) :
    algebraMap (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ))
      (FractionRing (MvPolynomial S ℚ)) z = coeffEmb S z := rfl

local instance smulCommCoeff :
    SMulCommClass (Equiv.Perm S) (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ))
      (FractionRing (MvPolynomial S ℚ)) := by
  constructor
  intro g z x
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', algebraMap_coeff_eq, smul_coeffEmb]

/-- **Fundamental theorem of symmetric rational functions.**  A rational function in the
variables `x_s` invariant under all permutations of `S` is a rational function of the
elementary symmetric polynomials `e₁, …, eₙ`. -/
theorem isInvariant_coeff :
    Algebra.IsInvariant (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ))
      (FractionRing (MvPolynomial S ℚ)) (Equiv.Perm S) := by
  classical
  constructor
  intro b hb
  obtain ⟨p, q, hqmem, hpq⟩ := IsFractionRing.div_surjective (MvPolynomial S ℚ) b
  have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hqmem
  have hsmul_prod : ∀ (g : Equiv.Perm S) (s : Finset (Equiv.Perm S))
      (f : Equiv.Perm S → MvPolynomial S ℚ), g • (∏ h ∈ s, f h) = ∏ h ∈ s, g • f h := by
    intro g s f
    exact map_prod (MulSemiringAction.toRingHom (Equiv.Perm S) (MvPolynomial S ℚ) g) f s
  have hsmul_ne : ∀ g : Equiv.Perm S, g • q ≠ 0 := by
    intro g h
    apply hq0
    have := congrArg (fun z : MvPolynomial S ℚ => g⁻¹ • z) h
    simpa [inv_smul_smul] using this
  set X : MvPolynomial S ℚ := ∏ g ∈ (Finset.univ.erase (1 : Equiv.Perm S)), g • q with hXdef
  set Q : MvPolynomial S ℚ := ∏ g : Equiv.Perm S, g • q with hQdef
  have hQX : Q = q * X := by
    rw [hQdef, hXdef,
      ← Finset.mul_prod_erase Finset.univ (fun g : Equiv.Perm S => g • q) (Finset.mem_univ 1),
      one_smul]
  have hX0 : X ≠ 0 := by
    rw [hXdef]
    exact Finset.prod_ne_zero_iff.mpr fun g _ => hsmul_ne g
  have hQ0 : Q ≠ 0 := by rw [hQX]; exact mul_ne_zero hq0 hX0
  have hQinv : ∀ g : Equiv.Perm S, g • Q = Q := by
    intro g
    rw [hQdef, hsmul_prod]
    have h : (fun h : Equiv.Perm S => g • h • q) = (fun h : Equiv.Perm S => (g * h) • q) :=
      funext fun h => (mul_smul g h q).symm
    rw [h]
    exact Fintype.prod_equiv (Equiv.mulLeft g) (fun h => (g * h) • q) (fun h => h • q)
      (fun h => rfl)
  set r : MvPolynomial S ℚ := p * X with hrdef
  have hXF : algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hX0
  have hQF : algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) Q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQ0
  have hb' : b = algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) r
      / algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) Q := by
    rw [hrdef, hQX, map_mul, map_mul, mul_div_mul_right _ _ hXF, ← hpq]
  have key : algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) r
      = b * algebraMap (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) Q := by
    rw [hb', div_mul_cancel₀ _ hQF]
  have hrinv : ∀ g : Equiv.Perm S, g • r = r := by
    intro g
    refine IsFractionRing.injective (MvPolynomial S ℚ) (FractionRing (MvPolynomial S ℚ)) ?_
    rw [algebraMap_smul_eq, key, smul_mul', hb g, ← algebraMap_smul_eq, hQinv, ← key]
  have hrsym : r.IsSymmetric := fun e => by rw [← smul_poly_eq]; exact hrinv e
  have hQsym : Q.IsSymmetric := fun e => by rw [← smul_poly_eq]; exact hQinv e
  obtain ⟨u, hu⟩ := exists_coeffHom_of_isSymmetric S hrsym
  obtain ⟨v, hv⟩ := exists_coeffHom_of_isSymmetric S hQsym
  refine ⟨algebraMap _ _ u / algebraMap _ _ v, ?_⟩
  rw [algebraMap_coeff_eq, map_div₀, coeffEmb_algebraMap, coeffEmb_algebraMap, hu, hv, hb']

local instance isGaloisGroupCoeff :
    IsGaloisGroup (Equiv.Perm S) (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ))
      (FractionRing (MvPolynomial S ℚ)) where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := isInvariant_coeff S

/-- **The generic polynomial of degree `n` has Galois group `Sym(S)`.**  For a finite type `S`
with `n = #S`, the symmetric group `Sym(S)` is realizable over the field of rational functions
in `n` variables over `ℚ` (the variables being the coefficients `e₁, …, eₙ`). -/
theorem symmetric_generic_realizable :
    IsRealizable (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ)) (Equiv.Perm S) :=
  isRealizable_of_isGaloisGroup (Equiv.Perm S)
    (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ)) (FractionRing (MvPolynomial S ℚ))

end Symmetric

end GenericSymmetric

/-- **Symmetric groups are realizable over the field of generic coefficients.** -/
theorem solution {S : Type} [Fintype S] :
    IsRealizable (FractionRing (MvPolynomial (Fin (Fintype.card S)) ℚ)) (Equiv.Perm S) :=
  GenericSymmetric.symmetric_generic_realizable S
