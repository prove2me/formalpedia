-- Prove2me | solution 1 for OAI.ParityWL.WeightedWitness.testMass_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:14:45.806344+00:00
-- url     : https://prove2.me/submissions/b2a70501-9df4-4b3f-b81a-04fbbbd15ef5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Masses.lean:L174-L226
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.WeightedWitness.testMass_transfer. The node keeps its source
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

end Masses

section TemplateMass

open scoped Classical

variable {t : ℕ} {W : Type} [Fintype W] {F : SimpleGraph W}
variable {a : F →g template t}

end TemplateMass

section BoundaryTests

open scoped Classical

variable {A W : Type} [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

lemma WeightedWitness.testMass_coordinate (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y : Finset W) (p : W → Bit) :
    w.testMass Y u p = ∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · have h := w.coordinate x ⟨v, hx ▸ huv⟩
    simp only [hx, ↓reduceIte, true_and]
    rw [← h, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : a y = v <;> simp [hy]
  · simp [hx]

/-- Transfer of a tested type mass across a separator. The test vanishes on its
boundary representatives; target-type vertices are absent from the boundary.
This includes every boundary edge rather than dropping such edges. -/
lemma WeightedWitness.testMass_transfer (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W) (p q : W → Bit)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hv : ∀ x ∈ S, a x ≠ v)
    (hp : ∀ x ∈ S, a x = u → p x = 0)
    (hcompat : ∀ x y, F.Adj x y → a x = u → a y = v → p x = q y) :
    w.testMass Y u p = w.testMass Y v q := by
  rw [w.testMass_coordinate huv]
  have hr : (∑ x ∈ Y, ∑ y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0) =
      ∑ x ∈ Y, ∑ y ∈ Y,
        if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_cases hxy : F.Adj x y
    · have hn := hv y (hboundary x hx y hxy hy)
      simp [hn]
    · simp [w.supported x y hxy]
  rw [hr, Finset.sum_comm]
  have hr' : (∑ y ∈ Y, ∑ x ∈ Y,
      if a x = u ∧ a y = v then w.edge x y * p x else 0) =
      ∑ y ∈ Y, ∑ x,
        if a x = u ∧ a y = v then w.edge x y * p x else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    by_cases hxy : F.Adj y x
    · by_cases ha : a x = u
      · simp [hp x (hboundary y hy x hxy hx) ha]
      · simp [ha]
    · have hn : ¬ F.Adj x y := fun h => hxy h.symm
      simp [w.supported x y hn]
  rw [hr', w.testMass_coordinate huv.symm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : a x = u
  · by_cases hy : a y = v
    · simp only [hx, hy, and_self, ↓reduceIte]
      by_cases hxy : F.Adj x y
      · rw [w.symmetric, hcompat x y hxy hx hy]
      · rw [w.supported x y hxy, ← w.symmetric x y, w.supported x y hxy]
        simp
    · simp [hy]
  · simp [hx]

end BoundaryTests

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.WeightedWitness.testMass_transfer := @_root_.OAI.ParityWL.WeightedWitness.testMass_transfer
