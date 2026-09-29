-- Prove2me | solution 1 for HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv_congr_apply_eq_transport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/304224bd-17d2-5619-b6f7-1f46b9559dd7

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.PlaceTransport

namespace S3bAux

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem transport_algebraMap {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') (ℓ : L) :
    NumberField.PlaceTransport.transport σ h (algebraMap L (w.adicCompletion L) ℓ) =
      algebraMap L (w'.adicCompletion L) (σ ℓ) := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact NumberField.PlaceTransport.transport_coe σ h ((WithVal.equiv (w.valuation L)).symm ℓ)

theorem transport_algebraMap_adicCompletion (w w' : v.Extension (𝓞 L)) (h : σ • w.1 = w'.1)
    (c : v.adicCompletion K) :
    NumberField.PlaceTransport.transport σ h (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w'.1.adicCompletion L) c := by
  obtain ⟨c, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K v c
  induction c using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (((NumberField.PlaceTransport.continuous_transport σ h).comp
        (w.adicCompletionSemialgHom_continuous K L)).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))
      ((w'.adicCompletionSemialgHom_continuous K L).comp
        (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v))
  | ih a =>
  change NumberField.PlaceTransport.transport σ h (w.adicCompletionSemialgHom K L (a.ofVal : v.adicCompletion K)) =
    w'.adicCompletionSemialgHom K L (a.ofVal : v.adicCompletion K)
  rw [HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe, HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
  have e1 := transport_algebraMap K L σ h (algebraMap K L a.ofVal)
  rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion] at e1
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.commutes] at e1
  exact e1

end S3bAux

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (w w' : v.Extension (𝓞 L)) (h : σ • w.1 = w'.1)
    (y : L ⊗[K] v.adicCompletion K) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y) w' =
      NumberField.PlaceTransport.transport σ h
        (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul ℓ c =>
    have h1 : (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
        (ℓ ⊗ₜ[K] c) = σ ℓ ⊗ₜ[K] c := rfl
    rw [h1, HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv, AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply,
      HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply,
      map_mul, S3bAux.transport_algebraMap K L σ h, S3bAux.transport_algebraMap_adicCompletion K L v σ w w' h]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end S_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport
end P2MW
export P2MW.S_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport (solution)
