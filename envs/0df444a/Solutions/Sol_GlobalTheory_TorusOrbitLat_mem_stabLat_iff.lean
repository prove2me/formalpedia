-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.mem_stabLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:12.736137+00:00
-- url     : https://prove2.me/submissions/bfb01661-8fa4-4325-937e-d17667db74d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.TorusOrbitLat
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]
namespace GlobalTheory.TorusOrbitLat
theorem _root_.solution (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl
end GlobalTheory.TorusOrbitLat
