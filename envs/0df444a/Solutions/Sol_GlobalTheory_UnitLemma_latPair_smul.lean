-- Prove2me | solution 1 for GlobalTheory.UnitLemma.latPair_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:58:58.378023+00:00
-- url     : https://prove2.me/submissions/f9f39770-b919-4183-b957-74c3d1d1c93c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable (O : Type) [CommRing O] (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂]
  [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (p : LatPair O E g₁ g₂) :
    t • p = ((Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2) :
      LatPair O E g₁ g₂) := rfl
end GlobalTheory.UnitLemma
