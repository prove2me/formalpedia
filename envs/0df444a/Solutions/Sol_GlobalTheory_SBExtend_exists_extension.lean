-- Prove2me | solution 1 for GlobalTheory.SBExtend.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:41.687248+00:00
-- url     : https://prove2.me/submissions/77239c23-396b-476c-b75b-8ef095e720a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Theorems.Thm_GlobalTheory_SBExtend_exists_isCompact_isClopen_between
import Theorems.Thm_GlobalTheory_SBExtend_indicator_mem_SB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.SBExtend
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
namespace GlobalTheory.SBExtend
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (U Z : Set X), IsOpen U → Z ⊆ U → ∀ f : SB Z, ∃ F : SB X, (∀ z : Z, F.1 z = f.1 z) ∧ ∀ x, x ∉ U → F.1 x = 0 := by
  classical
  intro X _ _ _ _ U Z hU hZU f
  obtain ⟨f, hl, hs⟩ := f
  have hfin : (f '' tsupport f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hs
    have := (hl.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
    refine this.subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have h : ∀ c : ℂ, ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ V ⊆ U ∧
      (c ≠ 0 → ∀ z : Z, (z : X) ∈ V ↔ f z = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isClopen_empty, Set.empty_subset _, fun h => absurd hc h⟩
    have hcl := hl.isClopen_fiber c
    obtain ⟨W, hW, hWe⟩ := isOpen_induced_iff.1 hcl.isOpen
    have hcomp : IsCompact {z : Z | f z = c} :=
      hs.isCompact.of_isClosed_subset hcl.isClosed fun z hz =>
        subset_tsupport _ (by
          rw [Function.mem_support, show f z = c from hz]; exact hc)
    obtain ⟨V, hV1, hV2, hV3, hV4⟩ := exists_isCompact_isClopen_between
      (hcomp.image continuous_subtype_val) (hW.inter hU) (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨(hWe.symm ▸ hz : z ∈ Subtype.val ⁻¹' W), hZU z.2⟩)
    refine ⟨V, hV1, hV2, fun x hx => (hV4 hx).2, fun _ z => ⟨fun hz => ?_, fun hz => hV3 ⟨z, hz, rfl⟩⟩⟩
    have : z ∈ Subtype.val ⁻¹' W := (hV4 hz).1
    rw [hWe] at this
    exact this
  choose V hV1 hV2 hV3 hV4 using h
  refine ⟨⟨∑ c ∈ hfin.toFinset.erase 0, c • (V c).indicator fun _ => (1 : ℂ),
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (indicator_mem_SB (hV1 c) (hV2 c))⟩,
    fun z => ?_, fun x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (f z)]
    · by_cases hz : f z = 0
      · simp [hz]
      · rw [Set.indicator_of_mem ((hV4 _ hz z).2 rfl), mul_one]
    · intro c hc hne
      rw [Set.indicator_of_notMem (fun h => hne ((hV4 c (Finset.ne_of_mem_erase hc) z).1 h).symm),
        mul_zero]
    · intro hn
      by_cases hz : f z = 0
      · simp [hz]
      · exact absurd (Finset.mem_erase.2 ⟨hz, hfin.mem_toFinset.2 ⟨z, subset_tsupport _ hz, rfl⟩⟩) hn
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun c _ => by
      rw [Set.indicator_of_notMem (fun h => hx (hV3 c h)), mul_zero]
end GlobalTheory.SBExtend
