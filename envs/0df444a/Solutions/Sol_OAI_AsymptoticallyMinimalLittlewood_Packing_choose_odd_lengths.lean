-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:06:20.525473+00:00
-- url     : https://prove2.me/submissions/620711aa-3e84-4b87-8899-f41b8ee4fdb1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean:L13-L41
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks

-- ---- from OAI.Analysis.Littlewood.Chunks ----
namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

lemma choose_odd_lengths {J : Type uJ} [Fintype J] [Nonempty J]
    (w : J → ℝ) (hw : ∀ j, 0<w j) (hs : 2*∑ j, w j<1) :
    ∃ d : J → ℕ, ∀ i, w i < (2*(d i : ℝ)+1)/(2*∑ j, (2*(d j : ℝ)+1)) := by
  let r : ℝ := Fintype.card J
  have hr : 0<r := Nat.cast_pos.mpr Fintype.card_pos
  let M : ℝ := (3*r+1)/(1-2*∑ j, w j)
  have hM : 0<M := by dsimp [M]; positivity
  let d : J → ℕ := fun j ↦ ⌈M*w j⌉₊
  have hdi (i : J) : M*w i ≤ (d i : ℝ) := Nat.le_ceil _
  have hdi' (i : J) : (d i : ℝ)<M*w i+1 := Nat.ceil_lt_add_one (mul_pos hM (hw i)).le
  have hL : (∑ j, (2*(d j : ℝ)+1)) < M := by
    have hlt : (∑ j, (2*(d j : ℝ)+1)) < ∑ j, (2*(M*w j)+3) := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      intro j _; linarith [hdi' j]
    have he : (∑ j, (2*(M*w j)+3)) = 2*M*(∑ j, w j)+3*r := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul]
      dsimp [r]; ring
    rw [he] at hlt
    have heM : M*(1-2*∑ j, w j)=3*r+1 := by
      dsimp [M]; field_simp [ne_of_gt (sub_pos.mpr hs)]
    nlinarith
  refine ⟨d,?_⟩
  intro i
  have hL0 : 0<(∑ j, (2*(d j : ℝ)+1)) :=
    Finset.sum_pos (fun j _ ↦ by positivity) Finset.univ_nonempty
  rw [lt_div_iff₀ (by positivity)]
  have hmul := mul_lt_mul_of_pos_right hL (hw i)
  nlinarith [hdi i]

variable {r : ℕ}
end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uJ} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths.{uJ} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths.{uJ}
