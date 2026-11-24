-- Prove2me | solution 1 for GlobalTheory.exists_testRing_universal_partially_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:47.63507+00:00
-- url     : https://prove2.me/submissions/5bbf282c-58b0-4959-9976-b7dbf396b1be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTriangularFrameRingOverTestRing
import Theorems.Thm_GlobalTheory_reduced_finiteType_iff_testRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (σ : Type) [Finite σ]
    (D : σ → Prop) (p : TRing K) :
    ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (x : σ → A.R), (∀ i, D i → IsUnit (x i)) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T) (t : σ → T), (∀ i, D i → IsUnit (t i)) →
        ∃! k : A.R →ₐ[K] T, k.comp π = ψ ∧ ∀ i, k (x i) = t i := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨hft, hred⟩ := (reduced_finiteType_iff_testRing K).2 p
  let P := MvPolynomial σ p.R
  let f : P := ∏ i ∈ Finset.univ.filter D, MvPolynomial.X i
  let B := Localization.Away f
  have hPred : _root_.IsReduced P := ⟨fun q hq => by
    ext i
    exact IsReduced.eq_zero _ (MvPolynomial.isNilpotent_iff.1 hq i)⟩
  have hBred : _root_.IsReduced B := isReduced_localizationPreserves (Submonoid.powers f) B hPred
  have hPft : Algebra.FiniteType K P := Algebra.FiniteType.trans hft inferInstance
  have hBft : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans hPft (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) B)
  obtain ⟨A, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 B hBft hBred
  let emb : P →ₐ[K] B := IsScalarTower.toAlgHom K P B
  let c : p.R →ₐ[K] P := IsScalarTower.toAlgHom K p.R P
  refine ⟨A, (e.symm : B →ₐ[K] A.R).comp (emb.comp c), fun i => e.symm (emb (MvPolynomial.X i)), ?_, ?_⟩
  · intro i hi
    refine IsUnit.map e.symm ?_
    have hf : IsUnit (emb f) := IsLocalization.Away.algebraMap_isUnit f
    refine isUnit_of_dvd_unit (map_dvd emb ?_) hf
    exact Finset.dvd_prod_of_mem _ (by simp [hi])
  · intro T _ _ ψ t ht
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ t
    have hφ : IsUnit (φ f) := by
      simp only [f, map_prod]
      refine IsUnit.prod_iff.2 fun i hi => ?_
      simp only [φ, P, MvPolynomial.aevalTower_X]
      exact ht i (by simpa using hi)
    have hφ' : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hφ.pow n
    let k₀ : B →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers f) hφ'
    have hk₀ : ∀ q, k₀ (emb q) = φ q := fun q => IsLocalization.lift_eq hφ' q
    refine ⟨k₀.comp (e : A.R →ₐ[K] B), ⟨?_, ?_⟩, ?_⟩
    · refine AlgHom.ext fun r => ?_
      change k₀ (e (e.symm (emb (c r)))) = ψ r
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_algebraMap ψ t r
    · intro i
      change k₀ (e (e.symm (emb (MvPolynomial.X i)))) = t i
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_X ψ t i
    · rintro k ⟨h1, h2⟩
      have h3 : ∀ q, k (e.symm (emb q)) = φ q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C r =>
          have := AlgHom.congr_fun h1 r
          exact this.trans (MvPolynomial.aevalTower_algebraMap ψ t r).symm
        | add a b ha hb => simp only [map_add, ha, hb]
        | mul_X a i ha =>
          simp only [map_mul, ha, h2]
          rw [show φ (MvPolynomial.X i) = t i from MvPolynomial.aevalTower_X ψ t i]
      have h4 : (k.comp (e.symm : B →ₐ[K] A.R)).toRingHom = k₀.toRingHom :=
        IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun q => (h3 q).trans (hk₀ q).symm)
      refine AlgHom.ext fun a => ?_
      have := RingHom.congr_fun h4 (e a)
      simpa using this
end GlobalTheory
