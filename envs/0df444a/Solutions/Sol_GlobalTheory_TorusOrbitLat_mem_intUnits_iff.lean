-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.mem_intUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:12.067706+00:00
-- url     : https://prove2.me/submissions/1a0798ec-417f-4002-9704-fc1e24fd3bc2

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
theorem _root_.solution (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl
end GlobalTheory.TorusOrbitLat
