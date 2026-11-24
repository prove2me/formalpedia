-- Prove2me | solution 1 for GlobalTheory.residue_localization_surjective_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:33.334699+00:00
-- url     : https://prove2.me/submissions/f044e72b-a079-40d8-ab37-9e1ebb1aa3ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type} [CommRing S] (q : Ideal S) [q.IsMaximal] :
    Function.Surjective ((IsLocalRing.residue (Localization.AtPrime q)).comp (algebraMap S (Localization.AtPrime q))) := by
  intro y
  obtain ⟨x', hx'⟩ := (Ideal.bijective_algebraMap_quotient_residueField q).2 y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  refine ⟨x, ?_⟩
  rw [← hx', Ideal.algebraMap_quotient_residueField_mk]
  rfl
end GlobalTheory
