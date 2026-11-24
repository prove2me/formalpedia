-- Prove2me | solution 1 for GlobalTheory.SmoothPointFamily.exists_etale_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:15.678691+00:00
-- url     : https://prove2.me/submissions/bcd0fcad-6341-4e26-9486-c7706a78d744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
import Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_basis_away
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_etale_of_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential
namespace GlobalTheory.SmoothPointFamily
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S) (m : ℕ) (s : Fin m → S), g ∉ p ∧
      (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).Etale := by
  obtain ⟨g, m, s, b, hg, hb⟩ := exists_basis_away (R := R) p
  refine ⟨g, m, s, hg, ?_⟩
  letI : Algebra (MvPolynomial (Fin m) R) (Localization.Away g) :=
    (MvPolynomial.eval₂Hom (algebraMap R (Localization.Away g))
        fun i => algebraMap S (Localization.Away g) (s i)).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin m) R) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      simp
  haveI : Algebra.Smooth S (Localization.Away g) := Algebra.Smooth.of_isLocalization_Away g
  haveI : Algebra.Smooth R (Localization.Away g) := Algebra.Smooth.comp R S _
  refine GlobalTheory.EtaleCoordJacobian.etale_of_basis R (Localization.Away g) (Fin m) b fun i => ?_
  rw [hb, RingHom.algebraMap_toAlgebra]
  simp
end GlobalTheory.SmoothPointFamily
