-- Prove2me | solution 1 for GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:50.570413+00:00
-- url     : https://prove2.me/submissions/d10fde4f-9ba2-4770-8254-d5a47307d08f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIffForallMaximalSpectrumResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  constructor
  · intro h m
    have := h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this
  · intro h
    letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
    choose p hpm hp using fun m : MaximalSpectrum B.A => h m
    refine ⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩
    have hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal := by
      intro m
      rw [eval₂_finset_prod]
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      apply Ideal.mul_mem_right
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 := hp m
      have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)
      rw [Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1] at h2
      rw [← aeval_def]
      exact h2.symm
    set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)
    have hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A) := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)
    have hz : z ^ k = 0 := by
      have := Ideal.pow_mem_pow hj k
      rw [hk] at this
      simpa using this
    exact IsReduced.eq_zero z ⟨k, hz⟩
end GlobalTheory.UnitLemma
