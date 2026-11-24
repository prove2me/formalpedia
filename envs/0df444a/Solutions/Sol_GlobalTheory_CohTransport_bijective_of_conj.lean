-- Prove2me | solution 1 for GlobalTheory.CohTransport.bijective_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:35.412011+00:00
-- url     : https://prove2.me/submissions/0b53c61e-a0f0-48b8-ba9d-889a940eee7c

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualityClausesOfMulEquiv
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
noncomputable section
open GlobalTheory GlobalTheory.CohTransport
namespace GlobalTheory.CohTransport
theorem _root_.solution {R : Type*} [CommRing R] {A B C A' B' C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (b : A →ₗ[R] B →ₗ[R] C) (b' : A' →ₗ[R] B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (eC : C ≃ₗ[R] C') (h : ∀ a x, b' (eA a) (eB x) = eC (b a x)) (hb : Function.Bijective b') :
    Function.Bijective b := by
  have key : (⇑b' ∘ ⇑eA) = ⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b := by
    funext a
    refine LinearMap.ext fun x => ?_
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply]
    rw [← h, LinearEquiv.apply_symm_apply]
  have h2 : Function.Bijective (⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b) := key ▸ hb.comp eA.bijective
  exact (LinearEquiv.bijective _).of_comp_iff' _ |>.1 h2
end GlobalTheory.CohTransport
