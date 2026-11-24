-- Prove2me | solution 1 for GlobalTheory.formallyEtale_stalkMap_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:32.116875+00:00
-- url     : https://prove2.me/submissions/b439fa06-1328-4b2b-954f-b7b2b5ea7b6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Theorems.Thm_GlobalTheory_ringHom_formallyEtale_respectsIso
import Theorems.Thm_GlobalTheory_formallyEtale_localRingHom_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (g : X ⟶ Y) [Etale g] (x : X) :
    (g.stalkMap x).hom.FormallyEtale :=
  HasRingHomProperty.stalkMap_of_respectsIso (P := @Etale) (Q := RingHom.Etale)
    ringHom_formallyEtale_respectsIso
    (fun f hf J _ => formallyEtale_localRingHom_of_etale f hf J) ‹_› x
end GlobalTheory
