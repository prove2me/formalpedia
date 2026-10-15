-- Prove2me | solution 1 for OAI.BufferedIsing.energy_pinExtension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:43:40.137831+00:00
-- url     : https://prove2.me/submissions/625a5857-e524-441d-8b2c-732827237de7

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/PinnedMarginal.lean:L231-L257
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.energy_pinExtension. The node keeps its source
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
import Theorems.Thm_OAI_BufferedIsing_energy_pin_expansion

-- ---- from OAI.Probability.Ising.PinnedMarginal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma sum_kept {n : ℕ} (F : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ v : KeptVertex F, f v.val) = ∑ v : Fin n, if v ∉ F then f v else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun v => by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) f).symm

/-- Exact deletion of fixed sites: their incident bonds become finite real
fields, while only bonds with two free endpoints remain as interactions. -/
lemma energy_pinExtension {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    energy G h (pinExtension F τ σ) = pinConstant G h F τ +
      deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v) := by
  classical
  rw [energy_pin_expansion G h F τ _ (pinExtension_agrees F τ σ)]
  congr 1
  · congr 1
    unfold deletedEnergy keptEdges
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with he
    · simp only [pinExtension, extendKept, dite_eq_right he.1, dite_eq_right he.2, dite_eq_left he.1, dite_eq_left he.2]
    · rfl
  · have hs : (∑ v : KeptVertex F, pinField G h F τ v * spin (σ v)) =
        ∑ v : Fin n, if v ∉ F then
          (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
            G.coupling e * spin (τ (G.right e)) else 0) +
            ∑ e, if G.right e = v ∧ G.left e ∈ F then
              G.coupling e * spin (τ (G.left e)) else 0) *
              spin (pinExtension F τ σ v) else 0 := by
      rw [← sum_kept]
      simp only [pinField, pinExtension_apply]
    exact hs.symm

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    energy G h (pinExtension F τ σ) = pinConstant G h F τ +
      deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v) := by
  first
    | exact OAI.BufferedIsing.energy_pinExtension G h F τ σ
    | exact OAI.BufferedIsing.energy_pinExtension
    | (apply OAI.BufferedIsing.energy_pinExtension <;> assumption)
    | (intros; apply OAI.BufferedIsing.energy_pinExtension <;> assumption)
