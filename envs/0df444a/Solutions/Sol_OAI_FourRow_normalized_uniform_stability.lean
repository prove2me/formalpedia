-- Prove2me | solution 1 for OAI.FourRow.normalized_uniform_stability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:54:54.289386+00:00
-- url     : https://prove2.me/submissions/db8b60f3-7620-4dcc-b196-d09a12d0fd10

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Stability.lean:L169-L199
-- (upload_full_project.md Phase 4): solution for node OAI.FourRow.normalized_uniform_stability. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability
import Theorems.Thm_OAI_FourRow_pair_stability_one

-- ---- inline helpers from OAI.Combinatorics.Permanent.Stability ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
theorem rowDist_nonneg (a : Site → ℝ) : 0 ≤ rowDist a :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairSq_nonneg (a b : Site → ℝ) : 0 ≤ pairSq a b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem pairSq_identity (a b : Site → ℝ) :
    pairSq a b = rowSq a * rowSq b + rowDot a b ^ 2 -
      2 * ∑ j, (a j * b j) ^ 2 := by
  simp only [pairSq, pairEntries, rowSq, rowDot, Fin.sum_univ_six,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem pairSq_comm (a b : Site → ℝ) : pairSq a b = pairSq b a := by
  simp only [pairSq_identity, rowDot, mul_comm]

theorem pair_stability (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) :
    rowDist a + rowDist b ≤ 18 * (24 - pairSq a b) := by
  have h1 := pair_stability_one a b ha hb haq hbq
  have h2 := pair_stability_one b a hb ha hbq haq
  rw [pairSq_comm b a] at h2
  linarith

theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm f]
  exact Fintype.sum_prod_type _

theorem decompose4_two (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

theorem decompose4_three (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 3 = Equiv.swap 0 i (e 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 2

theorem decompose3_two (i : Fin 3) (e : Equiv.Perm (Fin 2)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

theorem permanent_pair_identity (f : Functions) :
    (∑ π : Perm, ∏ i, f i (π i)) =
      ∑ j : Fin 6, pairEntries (f 0) (f 1) j *
        pairEntries (f 2) (f 3) (Fin.rev j) := by
  change (∑ π : Equiv.Perm (Fin 4), ∏ i : Fin 4, f i (π i)) = _
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    Fin.prod_univ_four, pairEntries]
  simp [decompose4_two, decompose4_three, decompose3_two,
    Equiv.swap_apply_def, Fin.rev]
  ring

theorem pairSq_le (a b : Site → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (haq : rowSq a = 4) (hbq : rowSq b = 4) : pairSq a b ≤ 24 := by
  have h := pair_stability_one a b ha hb haq hbq
  have h0 := rowDist_nonneg a
  linarith

theorem uniform_expectation_eq (f : Functions) :
    permanentExpectation uniformLaw f = (∑ π : Perm, ∏ i, f i (π i)) / 24 := by
  simp only [permanentExpectation, uniformLaw, ← Finset.mul_sum]
  ring

end FourRow
end

end OAI

-- ---- hoisted node ----
open OAI OAI.FourRow
open scoped BigOperators

theorem solution (f : Functions)
    (hf : ∀ i j, 0 ≤ f i j) (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation uniformLaw f ≤ 1 - totalDist f / 1728 := by
  let P := permanentExpectation uniformLaw f
  let U := pairSq (f 0) (f 1)
  let V := pairSq (f 2) (f 3)
  have hU0 : 0 ≤ U := pairSq_nonneg _ _
  have hV0 : 0 ≤ V := pairSq_nonneg _ _
  have hU : U ≤ 24 := pairSq_le _ _ (hf 0) (hf 1) (hn 0) (hn 1)
  have hV : V ≤ 24 := pairSq_le _ _ (hf 2) (hf 3) (hn 2) (hn 3)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (pairEntries (f 0) (f 1)) (fun j => pairEntries (f 2) (f 3) (Fin.rev j))
  have hrev : (∑ j : Fin 6, pairEntries (f 2) (f 3) (Fin.rev j) ^ 2) = V :=
    Equiv.sum_comp Fin.revPerm (fun j => pairEntries (f 2) (f 3) j ^ 2)
  rw [← permanent_pair_identity, hrev] at hcs
  change (∑ π : Perm, ∏ i, f i (π i)) ^ 2 ≤ U * V at hcs
  have hP2 : 576 * P ^ 2 ≤ U * V := by
    dsimp [P]
    rw [uniform_expectation_eq]
    nlinarith [hcs]
  have hUV : U * V ≤ 12 * (U + V) := by
    nlinarith [mul_nonneg hU0 (show 0 ≤ 24 - V by linarith),
      mul_nonneg hV0 (show 0 ≤ 24 - U by linarith)]
  have hd : totalDist f ≤ 18 * (48 - U - V) := by
    have h1 := pair_stability _ _ (hf 0) (hf 1) (hn 0) (hn 1)
    have h2 := pair_stability _ _ (hf 2) (hf 3) (hn 2) (hn 3)
    simp only [totalDist, Fin.sum_univ_four]
    dsimp [U, V]
    linarith
  change P ≤ _
  nlinarith [sq_nonneg (P - 1)]
