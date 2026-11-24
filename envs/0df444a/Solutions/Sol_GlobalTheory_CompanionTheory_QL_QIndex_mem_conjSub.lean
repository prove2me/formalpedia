-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.mem_conjSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:27.932865+00:00
-- url     : https://prove2.me/submissions/07619c75-01c9-4d3b-b45b-b2a53531d496

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.QIndex
theorem _root_.solution {G : Type} [Group G] (H : Subgroup G) (d p : G) :
    p ∈ conjSub H d ↔ d * p * d⁻¹ ∈ H := by
  simp only [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩
end GlobalTheory.CompanionTheory.QL.QIndex
