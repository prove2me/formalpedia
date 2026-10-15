-- Prove2me | solution 1 for OAI.ParityWL.WeightedWitness.no_tags
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:24:45.01401+00:00
-- url     : https://prove2.me/submissions/9d5aff23-e8f0-452e-99a3-2c21041f5d47

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Witnesses.lean:L65-L85
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.WeightedWitness.no_tags. The node keeps its source
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

-- ---- from OAI.Combinatorics.ParityLifts.WeightedDual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section WeightedDual

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

lemma sum_subtype_indicator {I : Type} [Fintype I] {R : Type} [AddCommMonoid R]
    (p : I → Prop) [DecidablePred p] [Fintype {x // p x}] (v : I → R) :
    (∑ x : {x // p x}, v x) = ∑ x, if p x then v x else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp), Finset.sum_filter]

end WeightedDual

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

omit [Fintype A] in
lemma WeightedWitness.coordinate_neighbors (w : WeightedWitness T F a b)
    (x : W) (u : T.neighborSet (a x)) :
    (∑ y : F.neighborSet x, if a y = u.1 then w.edge x y else 0) = w.vertex x := by
  change (∑ y : {y // F.Adj x y}, if a y.1 = u.1 then w.edge x y.1 else 0) = _
  rw [sum_subtype_indicator (F.Adj x)
    (fun y => if a y = u.1 then w.edge x y else 0)]
  convert w.coordinate x u using 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : F.Adj x y
  · simp [h]
  · simp [h, w.supported x y h]

lemma WeightedWitness.tag_sum (w : WeightedWitness T F a b)
    (z : (x : W) → T.neighborSet (a x) → Bit) :
    (∑ x, w.vertex x * ∑ u, z x u) =
      ∑ d : F.Dart, w.edge d.fst d.snd * z d.fst ⟨a d.snd, a.map_adj d.adj⟩ := by
  have hx : ∀ x, w.vertex x * ∑ u, z x u =
      ∑ y : F.neighborSet x, w.edge x y * z x ⟨a y, a.map_adj y.2⟩ := by
    intro x
    rw [Finset.mul_sum]
    calc
      _ = ∑ u : T.neighborSet (a x),
          (∑ y : F.neighborSet x, if a y = u.1 then w.edge x y else 0) * z x u := by
        simp_rw [w.coordinate_neighbors]
      _ = ∑ y : F.neighborSet x, ∑ u : T.neighborSet (a x),
          if a y = u.1 then w.edge x y * z x u else 0 := by
        simp_rw [Finset.sum_mul, ite_mul, zero_mul]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        have he : ∀ u : T.neighborSet (a x),
            a y = u.1 ↔ u = ⟨a y, a.map_adj y.2⟩ := by
          intro u
          constructor
          · intro h; exact Subtype.ext h.symm
          · intro h; exact (congrArg Subtype.val h).symm
        simp [he]
  rw [Fintype.sum_congr _ _ hx]
  calc
    _ = ∑ d : (x : W) × F.neighborSet x,
        w.edge d.1 d.2 * z d.1 ⟨a d.2, a.map_adj d.2.2⟩ :=
      (Fintype.sum_sigma _).symm
    _ = _ := (Equiv.sum_comp (dartNeighborsEquiv F)
      (fun d : (x : W) × F.neighborSet x =>
        w.edge d.1 d.2 * z d.1 ⟨a d.2, a.map_adj d.2.2⟩)).symm

/-- A genuine dual certificate makes the source-indexed tag system inconsistent. -/
theorem WeightedWitness.no_tags (w : WeightedWitness T F a b)
    (z : (x : W) → T.neighborSet (a x) → Bit)
    (hz : ∀ x, ∑ u, z x u = b (a x))
    (he : ∀ x y (h : F.Adj x y),
      z x ⟨a y, a.map_adj h⟩ = z y ⟨a x, a.map_adj h.symm⟩) : False := by
  have h := w.tag_sum z
  simp_rw [hz] at h
  rw [w.odd] at h
  have hzero : (∑ d : F.Dart, w.edge d.fst d.snd *
      z d.fst ⟨a d.snd, a.map_adj d.adj⟩) = 0 := by
    apply Finset.sum_ninvolution SimpleGraph.Dart.symm
    · intro d
      change w.edge d.fst d.snd * z d.fst _ + w.edge d.snd d.fst * z d.snd _ = 0
      rw [w.symmetric d.fst d.snd, he d.fst d.snd d.adj]
      exact CharTwo.add_self_eq_zero _
    · intro d _
      exact d.symm_ne
    · simp
    · exact SimpleGraph.Dart.symm_symm
  exact one_ne_zero (h.trans hzero)

variable {V : Type} [Fintype V] {G : SimpleGraph V} {τ : G →g T} {φ : F →g G}

end WitnessConverse

section PositiveWitness

open scoped Classical

variable {t : ℕ} {C : ChoiceSystem t}

end PositiveWitness

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.WeightedWitness.no_tags := @_root_.OAI.ParityWL.WeightedWitness.no_tags
