-- Prove2me | solution 1 for GlobalTheory.ZMTFin.bijective_awayMap_of_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:52.316817+00:00
-- url     : https://prove2.me/submissions/7c4b64df-8dda-460b-89c1-ca873653251a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
import Theorems.Thm_GlobalTheory_T_awayMap_bijective_of_injective_of_range_eq_subalgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin
namespace GlobalTheory.ZMTFin
theorem _root_.solution (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (φ : A →+* B) (hφ : Function.Injective φ)
    (hC : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B) (hab : φ a = b)
    (h : ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) :
    Function.Bijective (Localization.awayMap φ a) :=
  GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h
end GlobalTheory.ZMTFin
