-- Prove2me | solution 1 for GlobalTheory.UnitLemma.stLat_smul_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:01:15.558978+00:00
-- url     : https://prove2.me/submissions/a73c38ad-0cc7-40ae-bcfd-dac893a9f1a1

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
variable (O : Type) [CommRing O] (E : Type) [Field E] {A : Type} [CommRing A] [Algebra O A] [Algebra E A]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (g : A) (t : Aˣ) (L : stLat O E g) :
    ((t • L : stLat O E g) : Submodule O A) = mulLat O (t : A) L := rfl
end GlobalTheory.UnitLemma
