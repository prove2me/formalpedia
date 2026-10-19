-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_active_average_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:01:18.577703+00:00
-- url     : https://prove2.me/submissions/9042d60f-443b-4514-b5a6-bb62ef56128a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean:L51-L100
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_active_average_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

theorem sub_le (f : PhaseCost G) (x y : G) : f (x-y) ≤ f x+f y := by
  simpa only [sub_eq_add_neg, f.neg] using f.add_le x (-y)

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.ExcludedSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem excludedPhaseHom_apply {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin m, p l k ∣ M) (z : MaskResidues m p l) (i : Fin m) :
    excludedPhaseHom m p M l hd z i = (∑ j, subcircle (hd j) (z j)) - subcircle (hd i) (z i) := by
  change (∑ j ∈ Finset.univ.erase i, subcircle (hd j) (z j)) = _
  exact (Finset.sum_erase_eq_sub (Finset.mem_univ i))

theorem excluded_active_average_lower {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues m p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ i j : Fin m, z i ≠ 0 → i ≠ j →
      Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) :
    (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
      f.average (excludedPhaseHom m p M l hd) x z := by
  classical
  let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
  let y (i : Fin m) := x+excludedPhaseHom m p M l hd z i
  let B := ∑ i : Fin m, f (y i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => f.nonneg _)
  have hpair (i j : Fin m) (hi : i ∈ A) (hij : i ≠ j) : Q ≤ f (y i)+f (y j) := by
    have he : subcircle (hd i) (z i)-subcircle (hd j) (z j) = y j-y i := by
      dsimp only [y]
      rw [excludedPhaseHom_apply, excludedPhaseHom_apply]
      abel
    exact (hq i j ((Finset.mem_filter.mp hi).2) hij).trans (by rw [he]; simpa [add_comm] using f.sub_le (y j) (y i))
  have hper (i : Fin m) (hi : i ∈ A) : ((m : ℝ) - 1)*Q ≤ (m:ℝ)*f (y i)+B := by
    have hh := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j hj =>
      hpair i j hi (Ne.symm (Finset.mem_erase.mp hj).1))
    have hsum : (∑ j ∈ Finset.univ.erase i, (f (y i)+f (y j))) ≤
        ∑ j : Fin m, (f (y i)+f (y j)) := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun j _ _ => add_nonneg (f.nonneg _) (f.nonneg _))
    have hcard : (Finset.univ.erase i).card = m-1 := by simp
    rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hh
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh.trans hsum
  have hs : A.card ≤ m := by simpa using Finset.card_le_card (Finset.subset_univ A)
  have hsum := Finset.sum_le_sum (s := A) hper
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hpart : (∑ i ∈ A, f (y i)) ≤ B := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) (fun _ _ _ => f.nonneg _)
  have hsreal : (A.card : ℝ) ≤ m := by exact_mod_cast hs
  have hmreal : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ha0 : (0:ℝ) ≤ A.card := by positivity
  have hsq : (A.card : ℝ)*Q ≤ 4*B := by
    have hupper : (m:ℝ)*(∑ i ∈ A, f (y i))+(A.card:ℝ)*B ≤ 2*m*B := by
      nlinarith [mul_le_mul_of_nonneg_left hpart (show (0 : ℝ) ≤ m by positivity),
        mul_le_mul_of_nonneg_right hsreal hB]
    have hbase : (A.card:ℝ)*((m : ℝ) - 1)*Q ≤ 2*m*B := by nlinarith
    have hnon : 0 ≤ (A.card:ℝ)*Q := mul_nonneg ha0 hQ
    nlinarith [mul_nonneg hnon (show (0:ℝ)≤(m : ℝ) - 2 by linarith)]
  change (A.card:ℝ)/(4*m)*Q ≤ B / Fintype.card (Fin m)
  rw [Fintype.card_fin]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < m)]
  calc
    _ = (A.card:ℝ)*Q/4 := by field_simp
    _ ≤ _ := by linarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_active_average_lower := @_root_.OAI.FiniteCircle.excluded_active_average_lower
