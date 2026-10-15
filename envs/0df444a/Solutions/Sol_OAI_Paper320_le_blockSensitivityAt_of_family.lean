-- Prove2me | solution 1 for OAI.Paper320.le_blockSensitivityAt_of_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:20:14.181499+00:00
-- url     : https://prove2.me/submissions/7cbf021f-c18c-4e85-a3d8-97e7a0b89575

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Basic.lean:L141-L162
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.le_blockSensitivityAt_of_family. The node keeps its source
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
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

section Finite

variable [Fintype I]

theorem le_blockSensitivityAt (f : (I → Bool) → Bool) (x : I → Bool)
    (blocks : Finset (Finset I))
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B)
    (hb : ∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) :
    blocks.card ≤ blockSensitivityAt f x := by
  have h := Finset.le_sup (s := (Finset.univ : Finset (Finset (Finset I))))
    (f := fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0) (Finset.mem_univ blocks)
  have hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := ⟨hd, hb⟩
  simpa only [blockSensitivityAt, ite_eq_left hv] using h

theorem le_blockSensitivityAt_of_family [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by
  have hinj : Function.Injective blocks := by
    intro k l hkl
    by_contra hnekl
    obtain ⟨i, hi⟩ := hne k
    exact Finset.disjoint_left.mp (hd hnekl) hi (by simpa [← hkl] using hi)
  have hcard := le_blockSensitivityAt f x (Finset.univ.image blocks)
    (by
      intro A hA B hB hAB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
      exact hd (fun h => hAB (congrArg blocks h)))
    (by
      intro B hB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨hne k, hb k⟩)
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hcard

end Finite
end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical
variable {I J K : Type}
variable [Fintype I]

theorem solution [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by
  first
    | exact OAI.Paper320.le_blockSensitivityAt_of_family f x blocks hne hd hb
    | exact OAI.Paper320.le_blockSensitivityAt_of_family
    | (apply OAI.Paper320.le_blockSensitivityAt_of_family <;> assumption)
    | (intros; apply OAI.Paper320.le_blockSensitivityAt_of_family <;> assumption)
