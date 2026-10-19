-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:56:25.768286+00:00
-- url     : https://prove2.me/submissions/4af8b3c4-d321-482a-85fc-07cc4b029416

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationProbability.lean:L86-L135
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_colored_advance
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_valid_advance

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.AdaptiveReveals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

namespace Scheme
variable (P : Scheme E V S)

omit [Countable E] in
theorem hit_empty (n : ℕ) (s : S) : P.hit n s ∅ = Set.univ := by
  induction n generalizing s with
  | zero => simp [hit]
  | succ n ih =>
    simp only [hit]
    cases P.vertex s <;> simp [ih]

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

namespace History
end History
end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.Exploration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Packet
variable {r : ℕ}
end Packet

namespace Exploration
variable {m : Model} {r : ℕ}
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Exploration
variable {m : Model} {r : ℕ}

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationInvariant ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem after_determined (s : Exploration m r) :
    ProductCylinder.DeterminedBy s.reveal (s.after) := by
  intro ω ω' he
  unfold after History.observe
  congr 1
  funext e
  by_cases hr : e ∈ s.reveal
  · simp only [replace,ite_eq_left hr,he e hr]
  · simp only [replace,ite_eq_right hr]

theorem markedBad_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.markedBad q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [markedBad,hq,ha]

theorem advance_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.advance q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [advance,hq,h,ha]

end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem advance_processed (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).processed = insert t.vertex s.processed := by simp only [advance,hq]

theorem good_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.good ⊆ (s.advance q δ ω).good := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem Colored.bad_processed {s : Exploration m r} (h : s.Colored) : s.bad ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_right

theorem run_succ_right (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = (run q δ n s ω).advance q δ ω := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run_succ,ih,run_succ]

theorem run_colored {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Colored := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (valid_advance hs ω) (colored_advance hs hc ω)

theorem run_good_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).good) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact good_advance_mono _ _ _ _

theorem run_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r} (hs : s.queue = [])
    (n : ℕ) (ω : m.Config) : run q δ n s ω = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,advance_empty s q δ ω hs,ih]

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem hit_of_bad_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) (U : Finset Point)
    (hd : Disjoint U s.processed) (hU : U ⊆ (run q δ n s ω).bad) :
    ω ∈ (scheme (r := r) q δ).hit n s U := by
  induction n generalizing s U with
  | zero =>
    have he : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
    rw [he,AdaptiveReveals.Scheme.hit_empty]
    trivial
  | succ n ih =>
    cases hq : s.queue with
    | nil =>
      have he : U = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        rw [run_empty q δ hq] at hU
        exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
      rw [he,AdaptiveReveals.Scheme.hit_empty]
      trivial
    | cons t ts =>
      have hchild : (scheme (r := r) q δ).child s (s.reveal.restrict ω) = s.advance q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.advance_determined q δ) ω).symm
      have hbad : (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = s.markedBad q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω).symm
      have hv : (scheme (r := r) q δ).vertex s = some t.vertex := by simp only [scheme,hq,List.head?_cons,Option.map_some]
      rw [AdaptiveReveals.Scheme.hit,hv]
      change (t.vertex ∈ U → (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = true) ∧
        ω ∈ (scheme (r := r) q δ).hit n
          ((scheme (r := r) q δ).child s (s.reveal.restrict ω)) (U.erase t.vertex)
      rw [hchild,hbad]
      constructor
      · intro hv
        have hna : ¬s.Accept q δ t ω := by
          intro ha
          have hg : t.vertex ∈ (s.advance q δ ω).good := by
            simp only [advance,hq,ite_eq_left ha]; exact Finset.mem_insert_self _ _
          have hg' := run_good_mono q δ (s.advance q δ ω) ω (Nat.zero_le n) hg
          exact Finset.disjoint_left.mp (run_colored hs hc (n+1) ω).disjoint hg' (hU hv)
        simpa only [markedBad,hq,decide_eq_true_eq] using hna
      · apply ih (valid_advance hs ω) (colored_advance hs hc ω) (U.erase t.vertex)
        · apply Finset.disjoint_left.mpr
          intro v hv hp
          rw [advance_processed s q δ ω hq,Finset.mem_insert] at hp
          rcases hp with he|hp
          · exact (Finset.mem_erase.mp hv).1 he
          · exact Finset.disjoint_left.mp hd (Finset.mem_of_mem_erase hv) hp
        · exact Finset.Subset.trans (Finset.erase_subset _ _) hU

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset := @_root_.OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset
