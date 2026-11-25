-- Prove2me | solution 1 for GlobalTheory.covolume_le_sum_volume_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:26.069567+00:00
-- url     : https://prove2.me/submissions/90c5afa0-4b76-42a7-bc8e-f710a9c70505

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CovolumeLeSumVolumeOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory
open Pointwise
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (κ : Type) (T : Finset κ) (A : κ → Set (ι → ℝ))
    (_hA : ∀ k, MeasurableSet (A k))
    (hcov : ∀ t : ι → ℝ, ∃ k ∈ T, ∃ l ∈ L, t + l ∈ A k) :
    ENNReal.ofReal (ZLattice.covolume L volume) ≤ ∑ k ∈ T, volume (A k) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (ι → ℝ))
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hFdef
  haveI : Countable L := b.repr.toEquiv.countable_iff.2 inferInstance
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  refine le_trans ENNReal.ofReal_toReal_le ?_
  refine le_trans ?_ (measure_biUnion_finset_le T A)
  set U := ⋃ k ∈ T, A k with hU
  haveI : MeasurableConstVAdd L (ι → ℝ) :=
    ⟨fun c => by
      change Measurable fun x : ι → ℝ => (c : ι → ℝ) + x
      exact measurable_const_add _⟩
  haveI : VAddInvariantMeasure L (ι → ℝ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : ι → ℝ) s⟩
  rw [hF.measure_eq_tsum U]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro t ht
  obtain ⟨k, hk, l, hl, htl⟩ := hcov t
  refine Set.mem_iUnion.2 ⟨-(⟨l, hl⟩ : L), ?_, ht⟩
  rw [Set.mem_neg_vadd_set_iff]
  have : (⟨l, hl⟩ : L) +ᵥ t = t + l := by
    change l + t = t + l
    exact add_comm _ _
  rw [this]
  exact Set.mem_biUnion hk htl
end GlobalTheory
