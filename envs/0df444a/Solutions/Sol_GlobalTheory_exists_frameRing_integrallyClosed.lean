-- Prove2me | solution 1 for GlobalTheory.exists_frameRing_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:17.212797+00:00
-- url     : https://prove2.me/submissions/94507551-3cf2-497d-86d9-f4015f108d5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedMvPolynomialOfFinite
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_mvPolynomial_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Frames
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra K R], ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (_ : IsDomain A) (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), IsIntegrallyClosed A ∧ FrameRing m π X s := by
  intro K _ J _ m R _ _ _ _
  let σ := Option (Σ τ, Fin (m τ) × Fin (m τ))
  let P := MvPolynomial σ R
  let Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P := fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)
  let d : P := MvPolynomial.X none * ∏ τ, (Y τ).det
  let A := Localization.Away d
  have hd : IsUnit (algebraMap P A d) := IsLocalization.Away.algebraMap_isUnit d
  have hs : IsUnit (algebraMap P A (MvPolynomial.X none)) := by
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd
  have hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det) := by
    intro τ
    have h0 : (Y τ).det ∣ d :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd
  have hd0 : d ≠ 0 := by
    intro h0
    let w : σ → R := fun o => Option.elim o 1 (fun x => (1 : Matrix (Fin (m x.1)) (Fin (m x.1)) R) x.2.1 x.2.2)
    let ev : P →+* R := MvPolynomial.eval w
    have h1 : ∀ τ, ev.mapMatrix (Y τ) = 1 := by
      intro τ; ext i j
      simp [ev, Y, w, P]
    have h2 : ev d = 1 := by
      simp only [d, map_mul, map_prod, RingHom.map_det, h1, Matrix.det_one, Finset.prod_const_one, mul_one]
      simp [ev, w, P]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  have hle : Submonoid.powers d ≤ nonZeroDivisors P := powers_le_nonZeroDivisors_of_noZeroDivisors hd0
  have hdom : IsDomain A := IsLocalization.isDomain_localization hle
  have hP : IsIntegrallyClosed P := isIntegrallyClosed_mvPolynomial_of_finite σ R
  have hA : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A _ hle
  refine ⟨A, inferInstance, inferInstance, hdom, IsScalarTower.toAlgHom K R A,
    fun τ => (Y τ).map (algebraMap P A), hs.unit, hA, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := hY τ
    rw [RingHom.map_det] at this
    exact this
  · let v : σ → T := fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ v
    have hφY : ∀ τ, (Y τ).map φ = g τ := by
      intro τ; ext i j
      simp [φ, Y, v, P]
    have hφs : φ (MvPolynomial.X none) = a := by simp [φ, v, P]
    have hφd : IsUnit (φ d) := by
      simp only [d, map_mul, map_prod, hφs]
      refine a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)
      rw [AlgHom.map_det]
      have := hg τ
      rw [← hφY τ] at this
      exact this
    let k : A →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by
      rintro ⟨_, n, rfl⟩
      simpa using hφd.pow n)
    have hk : ∀ x : P, k (algebraMap P A x) = φ x := fun x => by simp [k]
    refine ⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · ext x
      change k (algebraMap R A x) = ψ x
      rw [IsScalarTower.algebraMap_apply R P A, hk]
      simp [φ, P]
    · rw [← hφY τ]; ext i j; simp [hk]
    · simp [hk, hφs]
    · rintro k' ⟨h1, h2, h3⟩
      have key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)
        · have := AlgHom.congr_fun h1 r
          change k' (algebraMap R A r) = ψ r at this
          rw [IsScalarTower.algebraMap_apply R P A] at this
          have h' : φ (MvPolynomial.C r) = ψ r := by simp [φ, P]
          exact this.trans h'.symm
        · rcases o with _ | ⟨τ, i, j⟩
          · exact h3.trans hφs.symm
          · have a1 := congrFun (congrFun (h2 τ) i) j
            have a2 := congrFun (congrFun (hφY τ) i) j
            exact a1.trans a2.symm
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      rw [key]
      ext x
      · exact (hk _).symm
      · exact (hk _).symm
end GlobalTheory
