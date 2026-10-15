-- Prove2me | solution 1 for OAI.ParityWL.WeightedWitness.mass_separator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:11:29.155505+00:00
-- url     : https://prove2.me/submissions/fb58fb72-6870-4330-9728-c6d098faafc7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Masses.lean:L60-L85
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.WeightedWitness.mass_separator. The node keeps its source
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

/-- Two types absent from the boundary of a separated vertex set have equal mass. -/
lemma WeightedWitness.mass_separator (w : WeightedWitness T F a b)
    {u v : A} (huv : T.Adj u v) (Y S : Finset W)
    (hboundary : ∀ x ∈ Y, ∀ y, F.Adj x y → y ∉ Y → y ∈ S)
    (hu : ∀ x ∈ S, a x ≠ u) (hv : ∀ x ∈ S, a x ≠ v) :
    w.mass Y u = w.mass Y v := by
  have restrict : ∀ (q r : A), T.Adj q r → (∀ x ∈ S, a x ≠ r) →
      w.mass Y q = ∑ x ∈ Y, ∑ y ∈ Y,
        if a x = q ∧ a y = r then w.edge x y else 0 := by
    intro q r hqr hr
    rw [w.coordinate_mass hqr]
    apply Finset.sum_congr rfl
    intro x hx
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_cases hy' : a y = r
    · have hn : ¬ F.Adj x y := fun hxy => hr y (hboundary x hx y hxy hy) hy'
      simp [w.supported x y hn]
    · simp [hy']
  rw [restrict u v huv hv, restrict v u huv.symm hu, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp [and_comm, w.symmetric]

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

end BoundaryTests

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.WeightedWitness.mass_separator := @_root_.OAI.ParityWL.WeightedWitness.mass_separator
