-- Prove2me | solution 1 for GlobalTheory.NormalDescent.normCoeff_map_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:21.795411+00:00
-- url     : https://prove2.me/submissions/1004c75e-6b95-4a8f-a0f9-cec44a300eb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCharpolyBaseChangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffMapOfIsPushout
import Theorems.Thm_GlobalTheory_NormalDescent_reverse_map_of_injective
import Theorems.Thm_GlobalTheory_NormalDescent_algebraMap_normCoeff
import Theorems.Thm_GlobalTheory_T_charpolyMulBaseChangeFinite_map_of_isPushout
import Theorems.Thm_GlobalTheory_T_exists_charpoly_baseChange_integrallyClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  have hbc := @GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
  have hint := @GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed
  let ι : FractionRing A →+* FractionRing A' := IsLocalization.map (FractionRing A') α
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective α hα)
  have hι : ∀ a : A, ι (algebraMap A (FractionRing A) a) = algebraMap A' (FractionRing A') (α a) :=
    fun a => IsLocalization.map_eq _ _
  have hc := hbc φ α β φ' H hφ hφ' ι hι b
  have spec : ∀ {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] (ψ : R →+* S)
      (hψ : ψ.Finite) (s : S), algebraMap R (FractionRing R) (normCoeff ψ hψ s k) =
        (charK ψ hψ (FractionRing R) s).reverse.coeff k := by
    intro R S _ _ _ _ ψ hψ s
    obtain ⟨P, hP⟩ := hint (K := FractionRing R) ψ hψ s
    refine algebraMap_normCoeff ψ hψ s k ⟨P.reverse.coeff k, ?_⟩
    rw [← hP, reverse_map_of_injective _ (IsFractionRing.injective R (FractionRing R)), coeff_map]
  apply IsFractionRing.injective A' (FractionRing A')
  rw [← hι, spec, spec, hc, reverse_map_of_injective ι ι.injective, coeff_map]
end GlobalTheory.NormalDescent
