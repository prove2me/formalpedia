-- Prove2me | solution 1 for GlobalTheory.RhoProd.out_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:37.779778+00:00
-- url     : https://prove2.me/submissions/012b3057-798f-4d67-9629-3c3651682c82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.RhoProd
namespace GlobalTheory.RhoProd
theorem _root_.solution {G : Type} [Group G] (H : Subgroup G) (P : G → Prop)
    (hP : ∀ g h, h ∈ H → (P (g * h) ↔ P g)) (g : G) :
    P (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ↔ P g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh]; exact hP g h h.2
end GlobalTheory.RhoProd
