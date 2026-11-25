-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellRank_eq_of_le_of_cellHeight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:18.225244+00:00
-- url     : https://prove2.me/submissions/1ff0cf56-64df-449f-8d55-78689ba3a5af

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_clip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g x : GL (Fin n) F}
    (h : ∀ a b, cellRank β γ x a b ≤ cellRank β γ g a b)
    (hh : cellHeight β γ g ≤ cellHeight β γ x) : ∀ a b, cellRank β γ x a b = cellRank β γ g a b := by
  have hbox : ∀ a ∈ Finset.range (Finset.univ.sup β + 2),
      ∀ b ∈ Finset.range (Finset.univ.sup γ + 1), cellRank β γ x a b = cellRank β γ g a b := by
    by_contra hne
    push Not at hne
    obtain ⟨a, ha, b, hb, hne⟩ := hne
    have : cellHeight β γ x < cellHeight β γ g :=
      Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => h a b)
        ⟨a, ha, Finset.sum_lt_sum (fun b _ => h a b) ⟨b, hb, lt_of_le_of_ne (h a b) hne⟩⟩
    omega
  intro a b
  rw [cellRank_clip x, cellRank_clip g]
  apply hbox <;> rw [Finset.mem_range] <;> omega
end GroundTheory.Automorphic.Parabolic
