-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:20:17.969295+00:00
-- url     : https://prove2.me/submissions/1f6df948-aa91-415a-b886-3a82989854e4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L157-L174
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma test_energy_le {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  let F := T.familyOfFintype S hS hd
  have hb := pow_le_pow_left₀ (norm_nonneg (F.test u)) (T.test_le_primal F u) 2
  rw [EuclideanSpace.norm_sq_eq] at hb
  change (∑ i : Fin (Fintype.card κ),
    ‖∑ v ∈ S ((Fintype.equivFin κ).symm i), u v‖ ^ 2) ≤ _ at hb
  rw [(Fintype.equivFin κ).symm.sum_comp (fun i : κ => ‖∑ v ∈ S i, u v‖ ^ 2)] at hb
  simpa only [Real.norm_eq_abs, sq_abs] using hb

/-- Empty pieces in a partition may be discarded; they contribute no energy. -/
lemma test_energy_le_allow_empty {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (u : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ S i, u v) ^ 2) ≤ (T.primalSeminorm u) ^ 2 := by
  classical
  let K := {i : κ // (S i).Nonempty}
  have h := T.test_energy_le (fun i : K => S i.val) (fun i => hS _ i.property)
    (by intro i j hij; exact hd (fun he => hij (Subtype.ext he))) u
  have hz : (∑ i : {i : κ // ¬ (S i).Nonempty}, (∑ v ∈ S i.val, u v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : S i.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
    simp [hi]
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun i : κ => (S i).Nonempty) (fun i => (∑ v ∈ S i, u v) ^ 2)
  rw [hz, add_zero] at he
  rwa [← he]

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty := @_root_.OAI.DiamondDistortion.SegmentSystem.test_energy_le_allow_empty
