-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_comap_eq_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:53.708843+00:00
-- url     : https://prove2.me/submissions/2c045462-747f-4a55-9bdc-712be2c3f674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {K A B : Type*} [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] (φ : A →ₐ[K] B) (hφ : φ.toRingHom.IsIntegral)
    (p : A →ₐ[K] K) (hp : ∀ a, φ a = 0 → p a = 0) : ∃ q : B →ₐ[K] K, comap φ q = p := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  have hsurj : Function.Surjective p := fun c => ⟨algebraMap K A c, by simp⟩
  haveI : (RingHom.ker p).IsMaximal := RingHom.ker_isMaximal_of_surjective p hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) (RingHom.ker p) hp
  have hcomp : ∀ a, Ideal.Quotient.mk Q (φ a) = algebraMap K (B ⧸ Q) (p a) := by
    intro a
    have : a - algebraMap K A (p a) ∈ Q.comap (algebraMap A B) := by
      rw [hQp]; simp [RingHom.mem_ker]
    have h2 : φ (a - algebraMap K A (p a)) ∈ Q := this
    rw [map_sub, AlgHom.commutes] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : Algebra.IsIntegral K (B ⧸ Q) := ⟨fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, hm, hb⟩ := hφ b
    refine ⟨h.map p.toRingHom, hm.map _, ?_⟩
    have : (algebraMap K (B ⧸ Q)).comp p.toRingHom = (Ideal.Quotient.mk Q).comp φ.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [eval₂_map, this, ← hom_eval₂, hb, map_zero]⟩
  let e : K ≃ₐ[K] (B ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext a
  change e.symm (Ideal.Quotient.mk Q (φ a)) = p a
  rw [hcomp, AlgEquiv.commutes]; rfl
end GlobalTheory.AffinePoints
