-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.convGrOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:25.354809+00:00
-- url     : https://prove2.me/submissions/b64cbb6e-f513-4706-86de-0ef50116edc2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_mem_stab
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_conv_of_line
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_conv_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution : BdetLaw → ExtLaw → ConvGrOf := by
  intro hB hE E R _ _ _ _ _ _ _ A hA hM ι _ _ s
  by_cases h0 : s = ∅
  · subst h0
    refine ⟨0, fun x _ => conv_top _ _ ?_ _⟩
    ext g
    simp [mem_stab]
  by_cases h1 : s = Set.univ
  · subst h1
    refine ⟨0, fun x _ => conv_top _ _ ?_ _⟩
    ext g
    simp [mem_stab]
  obtain ⟨f, rfl⟩ : ∃ f : Finset ι, (f : Set ι) = s := ⟨(Set.toFinite s).toFinset, by simp⟩
  obtain ⟨c, hc⟩ : ∃ c, c ∈ f := by
    by_contra hne
    exact h0 (by ext x; simp; exact fun hx => hne ⟨x, hx⟩)
  obtain ⟨r, hr⟩ : ∃ r, r ∉ f := by
    by_contra hne
    exact h1 (by ext x; simp; by_contra hx; exact hne ⟨x, hx⟩)
  let t₀ : Sub ι (Fin f.card) := ⟨f, by simp [Set.powersetCard]⟩
  let t₁ : Sub ι (Fin f.card) := ⟨insert r (f.erase c), by
    have : (insert r (f.erase c)).card = f.card := by
      rw [Finset.card_insert_of_notMem (fun h => hr (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem hc]
      have := Finset.card_pos.2 ⟨c, hc⟩
      omega
    simpa [Set.powersetCard] using this⟩
  have hne : t₀ ≠ t₁ := by
    intro e
    have h2 : r ∈ t₁.1 := Finset.mem_insert_self _ _
    rw [← e] at h2
    exact hr h2
  have h2 : 2 ≤ Fintype.card (Sub ι (Fin f.card)) := Fintype.one_lt_card_iff.2 ⟨t₀, t₁, hne⟩
  obtain ⟨R₀, D, Op, H, hW, -⟩ := (hM (Sub ι (Fin f.card)) t₀ t₀ h2).1 ℂ 1 continuous_const
  exact ⟨R₀, fun x hx => conv_of_line hB hE A hA.toGoodL t₀ x (hW.convR x hx)⟩
end GlobalTheory.CompanionTheory.Plucker
