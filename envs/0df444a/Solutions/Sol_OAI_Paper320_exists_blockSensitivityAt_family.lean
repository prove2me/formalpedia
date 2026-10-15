-- Prove2me | solution 1 for OAI.Paper320.exists_blockSensitivityAt_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:19:00.224669+00:00
-- url     : https://prove2.me/submissions/a52ef148-850a-4267-bb29-9ab92c5128e1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Basic.lean:L124-L139
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.exists_blockSensitivityAt_family. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

section Finite

variable [Fintype I]

theorem exists_blockSensitivityAt_family (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ blocks : Finset (Finset I), blocks.card = blockSensitivityAt f x ∧
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := by
  obtain ⟨blocks, _, hb⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Finset (Finset I))) (by simp)
    (fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0)
  by_cases hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
  · exact ⟨blocks, by simpa only [blockSensitivityAt, ite_eq_left hv] using hb.symm, hv⟩
  · have hz : blockSensitivityAt f x = 0 := by
      simpa only [blockSensitivityAt, ite_eq_right hv] using hb
    exact ⟨∅, by simp [hz], by simp, by simp⟩

end Finite
end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical
variable {I J K : Type}
variable [Fintype I]

theorem solution (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ blocks : Finset (Finset I), blocks.card = blockSensitivityAt f x ∧
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := by
  first
    | exact OAI.Paper320.exists_blockSensitivityAt_family f x
    | exact OAI.Paper320.exists_blockSensitivityAt_family
    | (apply OAI.Paper320.exists_blockSensitivityAt_family <;> assumption)
    | (intros; apply OAI.Paper320.exists_blockSensitivityAt_family <;> assumption)
