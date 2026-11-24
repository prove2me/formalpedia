-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.rep_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:27.85059+00:00
-- url     : https://prove2.me/submissions/ddbfc7a5-7957-480e-a1a6-7dc405a4dd48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {G : Type} [Group G] {P Γ : Subgroup G} (x : Γ) :
    ∃ δ : G, δ ∈ Γ ∧ δ ∈ P ∧ rep (Quotient.mk _ x : Cos P Γ) = δ * x := by
  have h : QuotientGroup.rightRel (P.subgroupOf Γ) (Quotient.out (Quotient.mk _ x : Cos P Γ)) x :=
    Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Γ)) x
  rw [QuotientGroup.rightRel_apply] at h
  refine ⟨((x * (Quotient.out (Quotient.mk _ x : Cos P Γ))⁻¹)⁻¹ : Γ), Subtype.property _, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp (inv_mem h))
  · simp [rep]
end GlobalTheory.CompanionTheory.RgEis
