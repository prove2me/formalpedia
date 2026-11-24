-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.comp_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:28.596199+00:00
-- url     : https://prove2.me/submissions/7dc885e0-370a-49d3-ac8c-bc770bc2c375

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] {a b : S → Y → Y} {g : Y → ℂ}
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution {a b : Y → Y} (ha : Continuous a) (hb : Continuous b) (h : ∀ y, b (a y) = y)
    (hg : g ∈ WeilM.SB Y) : (fun y => g (a y)) ∈ WeilM.SB Y := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hcl : ∀ {u : Y → ℂ}, IsLocallyConstant u → IsClosed (Function.support u) := fun hu => by
    exact (hu.isOpen_fiber 0).isClosed_compl
  have hc1 : IsClosed (Function.support fun y => g (a y)) := hcl (hg'.1.comp_continuous ha)
  have hc0 : IsCompact (Function.support g) := by
    have e : tsupport g = Function.support g := (hcl hg'.1).closure_eq
    rw [← e]
    exact hg'.2
  have hsub : (Function.support fun y => g (a y)) ⊆ b '' Function.support g :=
    fun y hy => ⟨a y, hy, h y⟩
  show IsLocallyConstant (fun y => g (a y)) ∧ HasCompactSupport (fun y => g (a y))
  refine ⟨hg'.1.comp_continuous ha, ?_⟩
  rw [HasCompactSupport, tsupport, hc1.closure_eq]
  exact (hc0.image hb).of_isClosed_subset hc1 hsub
end GlobalTheory.CompactAvgSchwartz
