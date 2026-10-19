-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_minimizer_options
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:02:52.552732+00:00
-- url     : https://prove2.me/submissions/f5daa5cb-bfdb-4ebd-a674-803288fe98c1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean:L131-L153
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_minimizer_options. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_excluded_active_average_lower

-- ---- from OAI.Combinatorics.FiniteCircle.ExcludedSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem excludedPhaseHom_apply {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin m, p l k ∣ M) (z : MaskResidues m p l) (i : Fin m) :
    excludedPhaseHom m p M l hd z i = (∑ j, subcircle (hd j) (z j)) - subcircle (hd i) (z i) := by
  change (∑ j ∈ Finset.univ.erase i, subcircle (hd j) (z j)) = _
  exact (Finset.sum_erase_eq_sub (Finset.mem_univ i))

 theorem excluded_inactive_average_lower {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hm : 0 < m) (hd : ∀ k : Fin m, p l k ∣ M)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues m p l)
    (hs : 2*(Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card ≤ m) :
    (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
      f.average (excludedPhaseHom m p M l hd) x z := by
  classical
  let A := Finset.univ.filter (fun k : Fin m => z k ≠ 0)
  let N := Finset.univ.filter (fun k : Fin m => z k = 0)
  let Q := f (x+∑ k,subcircle (hd k) (z k))
  have hQ : 0 ≤ Q := f.nonneg _
  have hsum : (N.card:ℝ)*Q ≤ ∑ k : Fin m, f (x+excludedPhaseHom m p M l hd z k) := by
    calc
      _ = ∑ _k ∈ N, Q := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ k ∈ N, f (x+excludedPhaseHom m p M l hd z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [excludedPhaseHom_apply, (Finset.mem_filter.mp hk).2, map_zero, sub_zero]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => f.nonneg _)
  have hcard : A.card+N.card = m := by
    simpa only [Finset.card_univ, Fintype.card_fin, not_not] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun k : Fin m => z k ≠ 0)
  change 2*A.card ≤ m at hs
  have hN : (m:ℝ) ≤ 2*N.card := by exact_mod_cast (show m ≤ 2*N.card by omega)
  rw [PhaseCost.average, Fintype.card_fin, le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)]
  change (1/4:ℝ)*Q*m ≤ _
  have hh := mul_le_mul_of_nonneg_right hN hQ
  nlinarith

 theorem excluded_minimizer_options {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin m, NeZero (p l k)]
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M) (hn : ∀ k : Fin m, 0 < p l k)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues m p l,
      (∀ Q : ℝ, 0 ≤ Q → (∀ i j : Fin m, z i ≠ 0 → i ≠ j →
        Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) →
        (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
          (f.step (excludedPhaseHom m p M l hd)) x) ∧
      (2*(Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card ≤ m →
        (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
          (f.step (excludedPhaseHom m p M l hd)) x) := by
  let : ∀ k : Fin m, NeZero (p l k) := fun k => ⟨(hn k).ne'⟩
  obtain ⟨z,hz⟩ := f.exists_average_eq (excludedPhaseHom m p M l hd) x
  refine ⟨z,?_,?_⟩
  · intro Q hQ hq
    change _ ≤ f.infAverage _ _
    rw [hz]
    exact excluded_active_average_lower hm hd f x z Q hQ hq
  · intro hs
    change _ ≤ f.infAverage _ _
    rw [hz]
    exact excluded_inactive_average_lower (by omega) hd f x z hs

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_minimizer_options := @_root_.OAI.FiniteCircle.excluded_minimizer_options
