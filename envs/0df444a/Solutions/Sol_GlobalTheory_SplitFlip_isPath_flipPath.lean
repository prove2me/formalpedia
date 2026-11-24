-- Prove2me | solution 1 for GlobalTheory.SplitFlip.isPath_flipPath
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:41.180227+00:00
-- url     : https://prove2.me/submissions/9ab2fdcb-03c2-46ac-bcf3-dc687768e402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
import Theorems.Thm_GlobalTheory_FlipPathPairwise_pairwise_of_isPath

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
open GlobalTheory.FlipPathPairwise
namespace GlobalTheory.SplitFlip
theorem _root_.solution : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
end GlobalTheory.SplitFlip
