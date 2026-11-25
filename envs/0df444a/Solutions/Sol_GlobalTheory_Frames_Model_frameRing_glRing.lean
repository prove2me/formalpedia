-- Prove2me | solution 1 for GlobalTheory.Frames.Model.frameRing_glRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:43:49.136082+00:00
-- url     : https://prove2.me/submissions/dafec121-6844-4349-bea3-6a3e6d79114e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_det_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
namespace GlobalTheory.Frames.Model
theorem _root_.solution : FrameRing m (glπ (K := K) m R) (glX m R) (glS m R) := by
  refine ⟨fun τ => IsUnit.of_mul_eq_one _ (det_rel m R τ), ?_⟩
  intro T _ _ ψ g a hg

  let v : Var m → T := fun
    | Sum.inl p => g p.1 p.2.1 p.2.2
    | Sum.inr (Sum.inl τ) => (((hg τ).unit⁻¹ : Tˣ) : T)
    | Sum.inr (Sum.inr true) => (a : T)
    | Sum.inr (Sum.inr false) => ((a⁻¹ : Tˣ) : T)
  let φ : MvPolynomial (Var m) R →ₐ[K] T :=
    { MvPolynomial.eval₂Hom (ψ : R →+* T) v with
      commutes' := fun r => by
        show MvPolynomial.eval₂ (ψ : R →+* T) v (algebraMap K _ r) = algebraMap K T r
        rw [IsScalarTower.algebraMap_apply K R (MvPolynomial (Var m) R), MvPolynomial.algebraMap_eq,
          MvPolynomial.eval₂_C]
        exact ψ.commutes r }
  have hφ : ∀ p, φ p = MvPolynomial.eval₂ (ψ : R →+* T) v p := fun _ => rfl
  have hgen : ∀ τ, (genMat m R τ).map φ = g τ := fun τ => by
    ext i j
    rw [Matrix.map_apply, hφ]
    unfold genMat
    rw [Matrix.of_apply, MvPolynomial.eval₂_X]

  have hle : rel m R ≤ RingHom.ker (φ : MvPolynomial (Var m) R →+* T) := by
    unfold rel
    rw [Ideal.span_le]
    rintro p (⟨τ, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show φ _ = 0
      rw [map_sub, map_mul, map_one, AlgHom.map_det, AlgHom.mapMatrix_apply, hgen τ, hφ, MvPolynomial.eval₂_X]
      exact sub_eq_zero.2 (IsUnit.mul_val_inv (hg τ))
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      show φ _ = 0
      rw [map_sub, map_mul, map_one, hφ, hφ, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X]
      exact sub_eq_zero.2 (Units.mul_inv a)
  have hI : ∀ p ∈ rel m R, φ p = 0 := fun p hp => RingHom.mem_ker.1 (hle hp)
  have hk : ∀ p, Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) p) =
      MvPolynomial.eval₂ (ψ : R →+* T) v p := fun _ => rfl
  refine ⟨Ideal.Quotient.liftₐ (rel m R) φ hI, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
  · ext r
    show Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.C r)) = ψ r
    rw [hk, MvPolynomial.eval₂_C]
    rfl
  · ext i j
    show Ideal.Quotient.liftₐ (rel m R) φ hI
      (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inl ⟨τ, i, j⟩))) = g τ i j
    exact (hk _).trans (MvPolynomial.eval₂_X _ _ _)
  · show Ideal.Quotient.liftₐ (rel m R) φ hI
      (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true)))) = (a : T)
    exact (hk _).trans (MvPolynomial.eval₂_X _ _ _)
  ·
    rintro k' ⟨h1, h2, h3⟩
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.coe_ringHom_injective
    apply MvPolynomial.ringHom_ext
    · intro r
      show k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.C r)) =
        Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.C r))
      rw [hk, MvPolynomial.eval₂_C]
      exact AlgHom.congr_fun h1 r
    · have ht : k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true)))) = a := h3
      rintro (⟨τ, i, j⟩ | τ | _ | _)
      · show k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inl ⟨τ, i, j⟩))) =
          Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inl ⟨τ, i, j⟩)))
        rw [hk, MvPolynomial.eval₂_X]
        exact congrFun (congrFun (h2 τ) i) j
      · show k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inl τ)))) =
          Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inl τ))))
        rw [hk, MvPolynomial.eval₂_X]
        have hd := congrArg k' (det_rel m R τ)
        rw [map_mul, map_one, AlgHom.map_det, AlgHom.mapMatrix_apply, h2 τ] at hd
        exact (Units.inv_eq_of_mul_eq_one_right (u := (hg τ).unit) hd).symm
      · show k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr false)))) =
          Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr false))))
        rw [hk, MvPolynomial.eval₂_X]
        have hu := congrArg k' (unit_rel m R)
        rw [map_mul, map_one, ht] at hu
        exact (Units.inv_eq_of_mul_eq_one_right hu).symm
      · show k' (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true)))) =
          Ideal.Quotient.liftₐ (rel m R) φ hI (Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inr true))))
        rw [hk, MvPolynomial.eval₂_X]
        exact ht
end GlobalTheory.Frames.Model
