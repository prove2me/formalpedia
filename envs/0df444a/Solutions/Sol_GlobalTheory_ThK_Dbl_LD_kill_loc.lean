-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.kill_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:21.906259+00:00
-- url     : https://prove2.me/submissions/896a7da5-e8e8-408e-bac8-c76e1469a3c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_cut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [T2Space V]
    (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ} (hφ : φ ∈ SB V)
    (h : ∀ x, φ x ≠ 0 → ∃ U ∈ 𝓝 x, ∀ ψ ∈ SB V, (∀ y ∉ U, ψ y = 0) → l ψ = 0) : l φ = 0 := by
  have hcl : IsClosed (Function.support φ) := (hφ.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support φ) := hφ.2.of_isClosed_subset hcl subset_closure
  have : ∃ A, IsClopen A ∧ Function.support φ ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0 := by
    refine hc.induction_on (p := fun s => ∃ A, IsClopen A ∧ s ⊆ A ∧ ∀ ψ ∈ SB V, (∀ y ∉ A, ψ y = 0) → l ψ = 0)
      ⟨∅, isClopen_empty, subset_rfl, fun ψ _ h => ?_⟩ ?_ ?_ ?_
    · rw [show ψ = 0 from funext fun y => h y (by simp), map_zero]
    · rintro s t hst ⟨A, h1, h2, h3⟩; exact ⟨A, h1, hst.trans h2, h3⟩
    · rintro s t ⟨A, h1, h2, h3⟩ ⟨B, k1, k2, k3⟩
      refine ⟨A ∪ B, h1.union k1, Set.union_subset_union h2 k2, fun ψ hψ h => ?_⟩
      rw [← Set.indicator_self_add_compl A ψ, map_add, h3 _ (sb_cut h1 hψ) (fun y hy => Set.indicator_of_notMem hy _),
        k3 _ (sb_cut h1.compl hψ), add_zero]
      intro y hy
      by_cases hA : y ∈ A
      · exact Set.indicator_of_notMem (not_not.2 hA) _
      · rw [Set.indicator_of_mem hA]; exact h y (not_or.2 ⟨hA, hy⟩)
    · intro x hx
      obtain ⟨U, hU, hl⟩ := h x hx
      have : (fun k => k + x) ⁻¹' U ∈ 𝓝 (0 : V) := (continuous_add_right x).continuousAt.preimage_mem_nhds (by simpa using hU)
      obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ this
      have hA : IsClopen ((fun y => y - x) ⁻¹' (K : Set V)) := K.isClopen.preimage (by fun_prop)
      refine ⟨_, mem_nhdsWithin_of_mem_nhds (hA.isOpen.mem_nhds (by simp)), _, hA, subset_rfl,
        fun ψ hψ h0 => hl ψ hψ fun y hy => h0 y fun hy' => hy ?_⟩
      simpa using hK hy'
  obtain ⟨A, -, h2, h3⟩ := this
  exact h3 φ hφ fun y hy => by_contra fun h => hy (h2 h)
end GlobalTheory.ThK.Dbl.LD
