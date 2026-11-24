-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.coe_mulLat_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:01.083044+00:00
-- url     : https://prove2.me/submissions/36341eda-e412-4f06-817a-2d4764ed2f9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeightedOrbitSumCongrCoefficientRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) (t : Aˣ) :
    (mulLat O' (t : A) L' : Set A) = mulLat O (t : A) L := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_mulLat, mem_mulLat, ← SetLike.mem_coe, h, SetLike.mem_coe]
end GlobalTheory.UnitLemma.Orbit
