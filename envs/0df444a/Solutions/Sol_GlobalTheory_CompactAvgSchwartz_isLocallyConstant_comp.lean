-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.isLocallyConstant_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:31.32686+00:00
-- url     : https://prove2.me/submissions/f2e51a2e-b57b-4721-a8dc-40859a53b643

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
theorem _root_.solution [CompactSpace S] (ha : Continuous fun p : S × Y => a p.1 p.2)
    (hb : Continuous fun p : S × Y => b p.1 p.2) (h : ∀ s y, b s (a s y) = y) (hg : g ∈ WeilM.SB Y) :
    IsLocallyConstant fun s y => g (a s y) := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hcl : IsClosed (Function.support g) := by
    exact (hg'.1.isOpen_fiber 0).isClosed_compl
  have hKc : IsCompact (Function.support g) := by
    have e : tsupport g = Function.support g := hcl.closure_eq
    rw [← e]
    exact hg'.2
  obtain ⟨C, hCc, hzero⟩ : ∃ C : Set Y, IsCompact C ∧ ∀ s y, y ∉ C → g (a s y) = 0 := by
    refine ⟨_, (isCompact_univ.prod hKc).image hb, fun s y hy => ?_⟩
    by_contra hne
    exact hy ⟨(s, a s y), ⟨Set.mem_univ _, hne⟩, h s y⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s₀
  have h1 : IsLocallyConstant fun p : S × Y => g (a p.1 p.2) := hg'.1.comp_continuous ha
  have h2 : IsLocallyConstant fun p : S × Y => g (a s₀ p.2) :=
    hg'.1.comp_continuous (ha.comp (continuous_const.prodMk continuous_snd))
  have hW : IsOpen {p : S × Y | g (a p.1 p.2) = g (a s₀ p.2)} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 h1 p,
      (IsLocallyConstant.iff_eventually_eq _).1 h2 p] with q hq1 hq2
    exact hq1.trans (hp.trans hq2.symm)
  have hsub : ({s₀} : Set S) ×ˢ C ⊆ {p : S × Y | g (a p.1 p.2) = g (a s₀ p.2)} := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    have e : s = s₀ := hs
    show g (a s y) = g (a s₀ y)
    rw [e]
  obtain ⟨u, v, hu, -, hsu, hCv, huv⟩ := generalized_tube_lemma isCompact_singleton hCc hW hsub
  filter_upwards [hu.mem_nhds (hsu (Set.mem_singleton s₀))] with s hs
  funext y
  by_cases hy : y ∈ C
  · exact huv (Set.mk_mem_prod hs (hCv hy))
  · rw [hzero s y hy, hzero s₀ y hy]
end GlobalTheory.CompactAvgSchwartz
