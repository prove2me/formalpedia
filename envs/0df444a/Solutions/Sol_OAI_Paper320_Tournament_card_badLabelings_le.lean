-- Prove2me | solution 1 for OAI.Paper320.Tournament.card_badLabelings_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:58:00.335992+00:00
-- url     : https://prove2.me/submissions/18a859cb-6a27-4582-a2bb-92efb631a9ff

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean:L69-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_badLabelings_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff

-- ---- from OAI.Combinatorics.Sensitivity.FixedCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Exact finite counting when a specified set of coordinates is fixed. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.LabelingEvents ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Exact counts of target-constant label constraints on sixteen vertices. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k r n : ℕ} (T : Tournament k)

theorem labelingEvent_eq [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    T.labelingEvent v m = Finset.univ.filter fun A =>
      ∀ p ∈ T.internalEdges (Finset.univ.image v), A p = m (Function.invFun v p.2) := by
  rw [labelingEvent, ite_eq_left hv]
  apply Finset.filter_congr
  intro A _
  simpa only [Finset.mem_univ, forall_const] using
    T.labelingConstraint_iff Finset.univ v m hv A

theorem card_labelingEvent [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    (T.labelingEvent v m).card = r ^ (k*k-n.choose 2) := by
  rw [T.labelingEvent_eq v m hv]
  have hc := card_fixedCoordinates (T.internalEdges (Finset.univ.image v))
    (fun p => m (Function.invFun v p.2))
  rw [T.card_internalEdges] at hc
  have hi : (Finset.univ.image v).card = n := by
    rw [Finset.card_image_of_injective _ hv]
    exact Fintype.card_fin n
  rw [hi] at hc
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc

theorem card_labelingEvent_le [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r) :
    (T.labelingEvent v m).card ≤ r ^ (k*k-n.choose 2) := by
  by_cases hv : Function.Injective v
  · exact (T.card_labelingEvent v m hv).le
  · simp only [labelingEvent, ite_eq_right hv, Finset.card_empty, Nat.zero_le]

theorem card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by
  calc
    (T.badLabelings n r).card ≤ ∑ v : Fin n → Fin k,
        (Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n → Fin k, ∑ _m : Fin n → Fin r, r^(k*k-n.choose 2) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ =>
        T.card_labelingEvent_le v m)
    _ = k^n * r^n * r^(k*k-n.choose 2) := by
      simp [Nat.mul_assoc]

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k r n : ℕ} (T : Tournament k)

theorem solution [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by
  first
    | exact OAI.Paper320.Tournament.card_badLabelings_le T
    | exact OAI.Paper320.Tournament.card_badLabelings_le
    | (apply OAI.Paper320.Tournament.card_badLabelings_le <;> assumption)
    | (intros; apply OAI.Paper320.Tournament.card_badLabelings_le <;> assumption)
