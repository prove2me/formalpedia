-- Prove2me | solution 1 for GlobalTheory.exists_algHom_ne_zero_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:14.928807+00:00
-- url     : https://prove2.me/submissions/781c9874-8019-468a-bec7-2207d2239d85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomNeZeroOfCountable
import Theorems.Thm_GlobalTheory_exists_eval_ne_zero_of_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by
  classical
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin
  have hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r} := by
    intro r hr
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ)
      (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r)
      (Algebra.IsIntegral.isIntegral r)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose! n hn0 hnr using hn
  have hne : ∀ r ∈ T, r ≠ 0 := fun r hr h => h0 (h ▸ hr)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by
    rintro ⟨r, hr, h⟩
    exact hn0 r (hne r hr) h)
  have hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ) :=
    fun z => ⟨MvPolynomial.C z, by simp⟩
  haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := E)
    (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by
      have : RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 hinj
      rw [this]
      exact bot_le)
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] (E ⧸ Q) := AlgEquiv.ofBijective _ hbij
  refine ⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩
  have h1 : Ideal.Quotient.mk Q r = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact h
  have h2 : r ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : n r ∈ Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) :=
    (Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr))
  rw [hQp] at h3
  exact hc (n r) ⟨r, hr, rfl⟩ h3
end GlobalTheory
