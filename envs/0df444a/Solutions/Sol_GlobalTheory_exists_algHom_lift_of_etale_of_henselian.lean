-- Prove2me | solution 1 for GlobalTheory.exists_algHom_lift_of_etale_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:38.380339+00:00
-- url     : https://prove2.me/submissions/11b094e8-a2d2-40bc-b435-b13f1b152f3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_etale_of_isLocalRing
import Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite_of_isLocalRing
import Theorems.Thm_GlobalTheory_henselianRing_of_finite
import Theorems.Thm_GlobalTheory_isLocalRing_quotient_one_sub
import Theorems.Thm_GlobalTheory_exists_completeOrthogonalIdempotents_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type*) {k A B : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing k] [CommRing A] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra k A] [Algebra k B] [Algebra.Etale k A] (J : Ideal B)
    (hJ : J ≤ (⊥ : Ideal B).jacobson) (φ : A →ₐ[k] B ⧸ J) :
    ∃ ψ : A →ₐ[k] B, ∀ a, Ideal.Quotient.mk J (ψ a) = φ a := by
  classical
  have := finite_maximalSpectrum_of_finite_of_isLocalRing R B
  have := Fintype.ofFinite (MaximalSpectrum B)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian R B
  have key : ∀ q : MaximalSpectrum B, ∃ ψ : A →ₐ[k] B ⧸ Ideal.span {1 - e q},
      ∀ a b, Ideal.Quotient.mk J b = φ a →
        ψ a - Ideal.Quotient.mk _ b ∈ J.map (Ideal.Quotient.mk _) := fun q ↦ by
    have := q.isMaximal
    have := isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
    let J' := J.map (Ideal.Quotient.mk (Ideal.span {1 - e q}))
    have : HenselianRing _ J' := henselianRing_of_finite R J' <| by
      refine Ideal.map_le_iff_le_comap.2 (hJ.trans ?_)
      rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
      exact Ideal.jacobson_mono bot_le
    obtain ⟨ψ, hψ⟩ := exists_algHom_lift_of_etale_of_isLocalRing J'
      ((Ideal.quotientMapₐ J' (Ideal.Quotient.mkₐ k _) Ideal.le_comap_map).comp φ)
    refine ⟨ψ, fun a b hb ↦ ?_⟩
    rw [← Ideal.Quotient.eq, hψ, AlgHom.comp_apply, ← hb]
    rfl
  choose ψ hψ using key
  let ε : B ≃ₐ[k] Π q, B ⧸ Ideal.span {1 - e q} :=
    .ofBijective (AlgHom.pi fun q ↦ Ideal.Quotient.mkₐ k _) he.bijective_pi
  refine ⟨ε.symm.toAlgHom.comp (AlgHom.pi ψ), fun a ↦ ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φ a)
  rw [← hb, Ideal.Quotient.eq]
  set c := (ε.symm.toAlgHom.comp (AlgHom.pi ψ)) a
  have hc : ∀ q, Ideal.Quotient.mk _ c = ψ q a := fun q ↦
    congr($(ε.apply_symm_apply (AlgHom.pi ψ a)) q)
  rw [← one_mul (c - b), ← he.complete, Finset.sum_mul]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  have := hψ q a b hb
  rw [← hc, ← map_sub, Ideal.mem_quotient_iff_mem_sup] at this
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 this
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have : e q * (c - b) = e q * y := by
    rw [← hyz]
    linear_combination (-w) * (he.idem q).eq
  rw [this]
  exact Ideal.mul_mem_left _ _ hy
end GlobalTheory
