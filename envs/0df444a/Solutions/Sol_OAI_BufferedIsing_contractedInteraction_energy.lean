-- Prove2me | solution 1 for OAI.BufferedIsing.contractedInteraction_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:48:49.86656+00:00
-- url     : https://prove2.me/submissions/b19b6e43-a761-4028-9e47-715057a5b9ca

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Contraction.lean:L197-L214
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.contractedInteraction_energy. The node keeps its source
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

-- ---- from OAI.Probability.Ising.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma quotientField_sum {V : Type*} [Fintype V] (S : Setoid V) (h : V → ℝ)
    (c : Quotient S → Bool) :
    (∑ q, quotientField S h q * spin (c q)) =
      ∑ v, h v * spin (c (Quotient.mk S v)) := by
  classical
  simp only [quotientField, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp

lemma contractedInteraction_energy {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (h : KeptVertex F → ℝ)
    (c : ContractedVertex G I J F → Bool) :
    interactionEnergy (contractedInteraction G I J F)
      (quotientField (comparisonSetoid G I J F ∅) h) c =
      deletedEnergy G F (fun v => c (Quotient.mk _ v)) +
        ∑ v, h v * spin (c (Quotient.mk _ v)) := by
  classical
  unfold interactionEnergy
  rw [quotientField_sum]
  congr 1
  unfold contractedInteraction deletedEnergy
  rw [Finset.sum_subtype (keptEdges G F) (fun e => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro e _
  simp only [extendKept, edgeLeftKept, edgeRightKept,
    dite_eq_left (Finset.mem_filter.mp e.property).2.1,
    dite_eq_left (Finset.mem_filter.mp e.property).2.2]

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (h : KeptVertex F → ℝ)
    (c : ContractedVertex G I J F → Bool) :
    interactionEnergy (contractedInteraction G I J F)
      (quotientField (comparisonSetoid G I J F ∅) h) c =
      deletedEnergy G F (fun v => c (Quotient.mk _ v)) +
        ∑ v, h v * spin (c (Quotient.mk _ v)) := by
  first
    | exact OAI.BufferedIsing.contractedInteraction_energy G I J F h c
    | exact OAI.BufferedIsing.contractedInteraction_energy
    | (apply OAI.BufferedIsing.contractedInteraction_energy <;> assumption)
    | (intros; apply OAI.BufferedIsing.contractedInteraction_energy <;> assumption)
