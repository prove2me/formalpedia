-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.influence_of_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:03:51.442469+00:00
-- url     : https://prove2.me/submissions/8e015a7b-878b-4fd6-9ec4-bc3267f843dd

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Influence.lean:L155-L217
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.influence_of_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence
import Theorems.Thm_OAI_BufferedIsing_DSS_influence_step
import Theorems.Thm_OAI_BufferedIsing_DSS_pin_comparison_of_removed

-- ---- from OAI.Probability.Ising.Influence ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

universe u

variable {V : Type u} [Fintype V]

/-- The influence inequality follows by induction on the vertex count and the positive-increment support size. -/
theorem influence_of_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (J : V → V → ℝ), (∀ u v, 0 ≤ J u v) → InfluenceBound J := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro V inst hcard J hJ
    have Hm : ∀ k (g h : V → ℝ), 0 ≤ h → (positiveSupport h).card = k → ∀ o : V,
        mean J (g + h) o - mean J (g - h) o ≤ mean J h o - mean J (-h) o := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ihk =>
        intro g h hh hk o
        by_cases hex : ∃ v, 0 < h v
        · obtain ⟨v, hv⟩ := hex
          let h0 : V → ℝ := fun u => if u = v then 0 else h u
          have hh0 : 0 ≤ h0 := by
            intro u
            dsimp [h0]
            split_ifs
            · exact le_rfl
            · exact hh u
          have hsupport : positiveSupport h0 = (positiveSupport h).erase v := by
            ext u
            by_cases hu : u = v
            · subst u
              simp [positiveSupport, h0]
            · simp [positiveSupport, h0, hu]
          have hsmall : (positiveSupport h0).card < k := by
            rw [hsupport, ← hk]
            apply Finset.card_erase_lt_of_mem
            simp [positiveSupport, hv]
          have Hfield : ∀ (g' : V → ℝ) (o' : V),
              mean J (g' + h0) o' - mean J (g' - h0) o' ≤ mean J h0 o' - mean J (-h0) o' := by
            intro g' o'
            exact ihk _ hsmall g' h0 hh0 rfl o'
          have hnsmall : Fintype.card {u : V // u ≠ v} < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := v) (by simp)
          have Hremoved : InfluenceBound (removedCoupling J v) :=
            ihn _ hnsmall {u : V // u ≠ v} rfl (removedCoupling J v) (fun u w => hJ u w)
          have Hpin := pin_comparison_of_removed J hJ g h0 hh0 v o Hremoved
          have Hstep := influence_step J hJ g h0 hh0 v o (h v) hv.le Hfield Hpin
          have he : h0 + fieldAt v (h v) = h := by
            ext u
            by_cases hu : u = v <;> simp [h0, fieldAt, hu]
          have hen : -h0 + fieldAt v (-h v) = -h := by
            ext u
            by_cases hu : u = v <;> simp [h0, fieldAt, hu]
          have hep : (g + h0) + fieldAt v (h v) = g + h := by rw [add_assoc, he]
          have hem : (g - h0) + fieldAt v (-h v) = g - h := by
            calc
              _ = g + (-h0 + fieldAt v (-h v)) := by abel
              _ = _ := by rw [hen]; rfl
          rw [hep, hem, he, hen] at Hstep
          exact Hstep
        · have hz : h = 0 := by
            ext u
            exact le_antisymm (le_of_not_gt (fun hu => hex ⟨u, hu⟩)) (hh u)
          subst h
          simp
    intro g h hh o
    exact Hm _ g h hh rfl o

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V]

theorem solution (n : ℕ) :
    ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (J : V → V → ℝ), (∀ u v, 0 ≤ J u v) → InfluenceBound J := by
  first
    | exact OAI.BufferedIsing.DSS.influence_of_card n
    | exact OAI.BufferedIsing.DSS.influence_of_card
    | (apply OAI.BufferedIsing.DSS.influence_of_card <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.influence_of_card <;> assumption)
