-- Prove2me | solution 1 for GlobalTheory.mk_mem_quotGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:30.07791+00:00
-- url     : https://prove2.me/submissions/0e338e72-cb1a-41a5-82d8-5fe79f52e4f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I d := ⟨a, ha, rfl⟩
end GlobalTheory
