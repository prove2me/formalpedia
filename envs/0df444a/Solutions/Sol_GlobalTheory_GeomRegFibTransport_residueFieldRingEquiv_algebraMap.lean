-- Prove2me | solution 1 for GlobalTheory.GeomRegFibTransport.residueFieldRingEquiv_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:06.839013+00:00
-- url     : https://prove2.me/submissions/d9f7dd95-b1f5-4b29-959e-49f3569915ec

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (P' : Ideal A') [P'.IsPrime] (a : A) :
    Ideal.residueFieldRingEquiv (P'.comap (e : A →+* A')) P' e rfl
      (algebraMap A (P'.comap (e : A →+* A')).ResidueField a) =
      algebraMap A' P'.ResidueField (e a) :=
  Ideal.ResidueField.map_algebraMap _ P' (e : A →+* A') rfl a
end GlobalTheory.GeomRegFibTransport
