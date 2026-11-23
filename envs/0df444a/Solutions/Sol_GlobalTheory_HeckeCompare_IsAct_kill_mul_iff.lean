-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.IsAct.kill_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:10.403747+00:00
-- url     : https://prove2.me/submissions/aa4b43fa-9b8f-48c8-bbe7-ea4242a6df6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}
namespace GlobalTheory.HeckeCompare
namespace IsAct
theorem _root_.solution (h : IsAct ρ) (p : ℕ) (I : Ideal O) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)} * I, ρ a x = 1) ↔ ∀ a ∈ I, ρ a (x ^ p) = 1 := by
  constructor
  · intro H a ha
    rw [← h.nat, ← h.2.1]
    exact H _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ha)
  · intro H a ha
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 ha
    rw [h.2.1, h.nat, H b hb]
end IsAct
end GlobalTheory.HeckeCompare
