-- Prove2me | solution 1 for OAI.ParityWL.WeightedWitness.main_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:13:13.787647+00:00
-- url     : https://prove2.me/submissions/2d381108-d078-46a3-af94-e3fee8e55796

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Masses.lean:L103-L116
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.WeightedWitness.main_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses

-- ---- from OAI.Combinatorics.ParityLifts.Masses ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Masses

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

lemma WeightedWitness.coordinate_mass (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y : Finset W) :
    w.mass Y u = ∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · have h := w.coordinate x ⟨v, hx ▸ huv⟩
    simpa [hx] using h.symm
  · simp [hx]

lemma WeightedWitness.mass_univ_adj (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) :
    w.mass Finset.univ u = w.mass Finset.univ v := by
  rw [w.coordinate_mass huv, w.coordinate_mass huv.symm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [and_comm, w.symmetric]

end Masses

section TemplateMass

open scoped Classical

lemma starParity_value {t : ℕ} (ht : 0 < t) (u : TemplateVertex t) :
    starParity t u = if u = .inl ⟨0, ht⟩ then 1 else 0 := by
  have hi : ∀ i : Fin t, i.val = 0 ↔ i = ⟨0, ht⟩ := by
    intro i
    exact (Fin.ext_iff (a := i) (b := ⟨0, ht⟩)).symm
  simp [starParity, hi]

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

lemma WeightedWitness.main_mass (w : WeightedWitness (template t) F a (starParity t))
    (ht : 0 < t) (i : Fin t) : w.mass Finset.univ (.inl i) = 1 := by
  have hz : w.mass Finset.univ (.inl ⟨0, ht⟩) = 1 := by
    calc
      _ = ∑ x, w.vertex x * starParity t (a x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [starParity_value ht]
        by_cases h : a x = .inl ⟨0, ht⟩ <;> simp [h]
      _ = 1 := w.odd
  by_cases hi : i = ⟨0, ht⟩
  · simpa [hi] using hz
  · have := w.mass_univ_adj (u := .inl i) (v := .inl ⟨0, ht⟩) hi
    exact this.trans hz

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

end BoundaryTests

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.WeightedWitness.main_mass := @_root_.OAI.ParityWL.WeightedWitness.main_mass
