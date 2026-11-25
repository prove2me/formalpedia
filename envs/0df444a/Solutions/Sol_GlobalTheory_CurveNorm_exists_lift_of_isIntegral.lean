-- Prove2me | solution 1 for GlobalTheory.CurveNorm.exists_lift_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:27.802189+00:00
-- url     : https://prove2.me/submissions/e7c07f5e-dea7-4be8-9e47-f3ce5951dfe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSmoothNormalisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CurveNorm
namespace GlobalTheory.CurveNorm
theorem _root_.solution {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by
  have hsurj : Function.Surjective e := fun c => ⟨algebraMap k E c, by simp⟩
  haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E')
    (RingHom.ker e) ⊥ (by
      intro x hx
      have : x = 0 := hinj (by simpa using hx)
      simp [this])
  have key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x) := by
    intro x
    have h1 : algebraMap k E (e x) - x ∈ RingHom.ker e := by simp [RingHom.mem_ker]
    rw [← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  haveI : Algebra.IsIntegral k (E' ⧸ Q) := by
    constructor
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp0⟩ := Algebra.IsIntegral.isIntegral (R := E) y
    refine ⟨p.map (e : E →+* k), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap k (E' ⧸ Q)).comp (e : E →+* k)
        = (Ideal.Quotient.mk Q).comp (algebraMap E E') := RingHom.ext key
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hbij : Function.Bijective (algebraMap k (E' ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : k ≃ₐ[k] (E' ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  refine ⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩
  ext x
  apply φ.injective
  exact (φ.apply_symm_apply _).trans (key x).symm
end GlobalTheory.CurveNorm
