-- Prove2me | solution 1 for GlobalTheory.NormalDescent.exists_map_eq_charK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:21.513207+00:00
-- url     : https://prove2.me/submissions/92fb69ec-39e9-4374-8b44-f371340feaef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosed
import Theorems.Thm_GlobalTheory_NormalDescent_charK_monic
import Theorems.Thm_GlobalTheory_T_charpoly_dvd_pow_finrank_of_aeval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  intro A B K _ _ _ _ _ _ _ φ hφ b
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  obtain ⟨g, hgm, hg⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  have hT : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (g.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap]
    have : (1 : K) ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b := rfl
    rw [this, Polynomial.aeval_algHom_apply, show aeval b g = 0 from hg, map_zero, map_zero]
  have hd := GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero _ _ hT
  rw [← Polynomial.map_pow] at hd
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hgm.pow _) hd
  refine ⟨P, ?_⟩
  have hm : (charK φ hφ K b).Monic := charK_monic φ hφ K b
  have : (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly = charK φ hφ K b := rfl
  rw [this, hm.leadingCoeff, C_1, mul_one] at hP
  exact hP
end GlobalTheory.NormalDescent
