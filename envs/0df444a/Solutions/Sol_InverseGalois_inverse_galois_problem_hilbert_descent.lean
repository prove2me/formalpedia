-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_hilbert_descent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T20:52:35.175154+00:00
-- url     : https://prove2.me/submissions/a15624bd-2285-4855-a873-8eacb47c5a9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InverseGalois_realizability
import Theorems.Thm_InverseGalois_hilbert_descent_multivariate

open InverseGalois

noncomputable section

namespace OneVarDescent

universe u v

/-- Realizability of a group over a field transports along a ring isomorphism of base fields. -/
theorem isRealizable_of_ringEquiv {K K' : Type u} [Field K] [Field K'] {G : Type v} [Group G]
    (e : K ≃+* K') (h : IsRealizable K G) : IsRealizable K' G := by
  obtain ⟨r⟩ := h.exists_realization
  letI : Field r.L := r.to_field
  letI : Algebra K r.L := r.to_algebra
  haveI : IsGalois K r.L := r.to_isGalois
  letI algK' : Algebra K' r.L := ((algebraMap K r.L).comp e.symm.toRingHom).toAlgebra
  have hmap : ∀ z : K', algebraMap K' r.L z = algebraMap K r.L (e.symm z) := fun _ => rfl
  have hmap' : ∀ k : K, algebraMap K r.L k = algebraMap K' r.L (e k) := by
    intro k; rw [hmap, e.symm_apply_apply]
  haveI : IsGalois K' r.L := by
    refine IsGalois.of_equiv_equiv (f := e) (g := RingEquiv.refl r.L) ?_
    ext k
    exact (hmap' k).symm
  let toK : (r.L ≃ₐ[K'] r.L) → (r.L ≃ₐ[K] r.L) := fun ψ =>
    AlgEquiv.ofRingEquiv (f := ψ.toRingEquiv) (fun k => by
      rw [hmap' k]; exact ψ.commutes (e k))
  let toK' : (r.L ≃ₐ[K] r.L) → (r.L ≃ₐ[K'] r.L) := fun ψ =>
    AlgEquiv.ofRingEquiv (f := ψ.toRingEquiv) (fun z => by
      rw [hmap z]; exact ψ.commutes (e.symm z))
  let φ : (r.L ≃ₐ[K'] r.L) ≃* (r.L ≃ₐ[K] r.L) :=
    { toFun := toK
      invFun := toK'
      left_inv := fun ψ => by ext x; rfl
      right_inv := fun ψ => by ext x; rfl
      map_mul' := fun ψ₁ ψ₂ => by ext x; rfl }
  exact ⟨⟨{ L := r.L
            to_field := r.to_field
            to_algebra := algK'
            to_isGalois := inferInstance
            iso := r.iso.trans φ.symm }⟩⟩

/-- `ℚ(t)` is the fraction field of the polynomial ring in one variable over `ℚ`. -/
def ratFuncEquiv : RatFunc ℚ ≃+* FractionRing (MvPolynomial (Fin 1) ℚ) :=
  (IsFractionRing.ringEquivOfRingEquiv
    (A := MvPolynomial (Fin 1) ℚ) (K := FractionRing (MvPolynomial (Fin 1) ℚ))
    (B := Polynomial ℚ) (L := RatFunc ℚ)
    (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingEquiv).symm

end OneVarDescent

/-- One-variable Hilbert descent is the case of one indeterminate of the
several-variable descent. -/
theorem solution {G : Type*} [Fintype G] [Group G] (h : IsRealizable (RatFunc ℚ) G) :
    IsRealizable ℚ G :=
  hilbert_descent_multivariate (I := Fin 1)
    (OneVarDescent.isRealizable_of_ringEquiv OneVarDescent.ratFuncEquiv h)
