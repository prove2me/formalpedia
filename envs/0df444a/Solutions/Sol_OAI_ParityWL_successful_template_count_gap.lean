-- Prove2me | solution 1 for OAI.ParityWL.successful_template_count_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:26:43.045473+00:00
-- url     : https://prove2.me/submissions/ce76e991-a272-40c5-bfe2-a5716a386688

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Witnesses.lean:L162-L181
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.successful_template_count_gap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Theorems.Thm_OAI_ParityWL_WeightedWitness_no_tags
import Theorems.Thm_OAI_ParityWL_homCount_lift_strict_iff
import Theorems.Thm_OAI_ParityWL_inconsistent_weightedWitness

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

lemma starParity_value {t : ℕ} (ht : 0 < t) (u : TemplateVertex t) :
    starParity t u = if u = .inl ⟨0, ht⟩ then 1 else 0 := by
  have hi : ∀ i : Fin t, i.val = 0 ↔ i = ⟨0, ht⟩ := by
    intro i
    exact (Fin.ext_iff (a := i) (b := ⟨0, ht⟩)).symm
  simp [starParity, hi]

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

-- ---- from OAI.Combinatorics.ParityLifts.Witnesses ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section WitnessConverse

open scoped Classical

variable {A W : Type} [Fintype A] [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

variable {V : Type} [Fintype V] {G : SimpleGraph V} {τ : G →g T} {φ : F →g G}

omit [Fintype V] in
theorem weightedWitness_inconsistent
    (w : WeightedWitness T F (τ.comp φ) b) :
    ¬ Nonempty (Solutions T G F τ φ b) := by
  rintro ⟨z⟩
  exact w.no_tags z.1 z.2.1 z.2.2

theorem homCount_lift_strict_iff_witness :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, Nonempty (WeightedWitness T F (τ.comp φ) b) := by
  rw [homCount_lift_strict_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, inconsistent_weightedWitness T G F τ φ b hφ⟩
  · rintro ⟨φ, ⟨w⟩⟩
    exact ⟨φ, weightedWitness_inconsistent w⟩

end WitnessConverse

section PositiveWitness

open scoped Classical

variable {t : ℕ} {C : ChoiceSystem t}

/-- The explicit noncancelling source is the uncolored template itself. -/
theorem successful_template_count_gap (ht : 0 < t) (hs : C.Successful) :
    homCount (template t) (starLift C) < homCount (template t) (zeroLift C) := by
  obtain ⟨d, hd⟩ := hs
  let φ := choiceMap d hd
  have hφ : ∀ v, ((baseProjection C).comp φ) v = v := choiceMap_type d hd
  apply homCount_lift_strict_iff_witness.mpr
  refine ⟨φ, ⟨{
    vertex := fun _ => 1
    edge := fun x y => if (template t).Adj x y then 1 else 0
    symmetric := by intro x y; simp [SimpleGraph.adj_comm]
    supported := by intro x y h; simp [h]
    coordinate := ?_
    odd := ?_ }⟩⟩
  · intro x u
    simp only [hφ]
    have hu : (template t).Adj x u.1 := by simpa [hφ] using u.2
    simp [hu]
  · simp only [one_mul, hφ]
    simp [starParity_value ht]

end PositiveWitness

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.successful_template_count_gap := @_root_.OAI.ParityWL.successful_template_count_gap
