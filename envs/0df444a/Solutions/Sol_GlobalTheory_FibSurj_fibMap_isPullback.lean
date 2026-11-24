-- Prove2me | solution 1 for GlobalTheory.FibSurj.fibMap_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:00.217254+00:00
-- url     : https://prove2.me/submissions/01726a57-183f-430e-b32f-f781a76b6fa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
import Theorems.Thm_GlobalTheory_FibSurj_fibMap_fst
import Theorems.Thm_GlobalTheory_FibSurj_fibMap_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.FibSurj
open IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))
namespace GlobalTheory.FibSurj
theorem _root_.solution :
    IsPullback (fibMap φ s) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (ResidueField.map φ))) := by
  have hL := IsPullback.of_hasPullback (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))
    (Spec.map (CommRingCat.ofHom (residue O)))
  have hR := IsPullback.of_hasPullback s (Spec.map (CommRingCat.ofHom φ))
  have hOut := hL.paste_horiz hR
  rw [← fibMap_fst, spec_square] at hOut
  exact IsPullback.of_right hOut (fibMap_snd φ s) (IsPullback.of_hasPullback _ _)
end GlobalTheory.FibSurj
