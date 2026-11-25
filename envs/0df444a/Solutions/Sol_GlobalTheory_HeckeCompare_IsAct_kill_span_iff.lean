-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.IsAct.kill_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:44.824095+00:00
-- url     : https://prove2.me/submissions/999b9345-0086-49a4-9c92-02dd62834a0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_nat
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_of_dvd
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_of_dvd


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
theorem _root_.solution (h : IsAct ρ) (p : ℕ) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)}, ρ a x = 1) ↔ x ^ p = 1 :=
  ⟨fun H => (h.nat p x).symm.trans (H _ (Ideal.mem_span_singleton_self _)),
    fun H _ ha => h.of_dvd H (Ideal.mem_span_singleton.1 ha)⟩
end IsAct
end GlobalTheory.HeckeCompare
