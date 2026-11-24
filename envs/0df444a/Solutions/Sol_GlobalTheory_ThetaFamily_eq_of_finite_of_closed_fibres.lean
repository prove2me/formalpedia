-- Prove2me | solution 1 for GlobalTheory.ThetaFamily.eq_of_finite_of_closed_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:29:55.903795+00:00
-- url     : https://prove2.me/submissions/103eeaf6-afe9-4b62-bc83-b049b7319656

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily
namespace GlobalTheory.ThetaFamily
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] {B : Set X} (hB : IsPreconnected B)
    {C : Set Y} (hC : C.Finite) (c : X → Y) (hc : ∀ b ∈ B, c b ∈ C)
    (h : ∀ k ∈ C, ∀ b ∈ B, b ∈ closure {b' ∈ B | c b' = k} → c b = k) : ∀ b ∈ B, ∀ b' ∈ B, c b = c b' := by
  have : PreconnectedSpace B := Subtype.preconnectedSpace hB
  have hl : IsLocallyConstant fun b : B => c b := fun s => by
    have e : ((fun b : B => c b) ⁻¹' s)ᶜ = ⋃ k ∈ C \ s, (Subtype.val ⁻¹' closure {b' ∈ B | c b' = k} : Set B) := by
      ext b
      simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_diff, exists_prop]
      exact ⟨fun hb => ⟨c b, ⟨hc b b.2, hb⟩, subset_closure ⟨b.2, rfl⟩⟩,
        fun ⟨k, hk, hb⟩ => (h k hk.1 b b.2 hb).symm ▸ hk.2⟩
    rw [← isClosed_compl_iff, e]
    exact (hC.subset diff_subset).isClosed_biUnion fun k _ => isClosed_closure.preimage continuous_subtype_val
  exact fun b hb b' hb' => hl.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨b', hb'⟩
end GlobalTheory.ThetaFamily
