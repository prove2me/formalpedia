-- Prove2me | solution 1 for Light.Wrap.small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:48.492175+00:00
-- url     : https://prove2.me/submissions/f3ca7f04-23d9-4720-a912-19e5b963d3ff

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
namespace Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
section OfEnd
variable {Q : EndStatement.Problem} (x : Bounded Q)
end OfEnd
private theorem polyBound_pow_le (s k κ n : ℕ) {r : ℕ} (hr : (κ + 1) * k ≤ r) :
    polyBound s k [n, n ^ κ] ≤ 2 ^ (s + k) * (n + 1) ^ r := by
  have hpos : 1 ≤ n + 1 := by omega
  have hU : n ^ κ + 1 ≤ 2 * (n + 1) ^ κ := by
    have h1 : n ^ κ ≤ (n + 1) ^ κ := Nat.pow_le_pow_left (by omega) κ
    have h2 : 1 ≤ (n + 1) ^ κ := Nat.one_le_pow _ _ hpos
    omega
  unfold polyBound
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc 2 ^ s * ((n + 1) * (n ^ κ + 1)) ^ k
      ≤ 2 ^ s * ((n + 1) * (2 * (n + 1) ^ κ)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hU) k)
    _ = 2 ^ (s + k) * (n + 1) ^ ((κ + 1) * k) := by
        rw [show (n + 1) * (2 * (n + 1) ^ κ) = 2 * (n + 1) ^ (κ + 1) by ring, mul_pow, ← pow_mul,
          pow_add]
        ring
    _ ≤ 2 ^ (s + k) * (n + 1) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos hr)
namespace Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
end Wrap
end Light
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
namespace Light.Wrap
theorem _root_.solution (w : Wrap Q task dec) {need : ℕ → ℕ → Need} (hpoly : PolyNeed need) (κ : ℕ) :
    ∃ s k : ℕ, ∀ x : Bounded Q, x.U = x.n ^ κ → Small s k [x.n] (w.limits need x) := by
  obtain ⟨s, k, hpoly⟩ := hpoly
  obtain ⟨r, hr⟩ : ∃ r, r = (κ + 1) * k + κ + 2 := ⟨_, rfl⟩
  refine ⟨s + k + 5 + Nat.size w.cst, r, fun x hU => ?_⟩
  obtain ⟨hword, hcells, hdepth⟩ := hpoly x.n x.U
  have hpos : 1 ≤ x.n + 1 := by omega
  have hneed := polyBound_pow_le s k κ x.n (r := r) (by omega)
  have hsquare : x.n * x.n + 1 ≤ (x.n + 1) ^ r :=
    (by nlinarith : x.n * x.n + 1 ≤ (x.n + 1) ^ 2).trans (Nat.pow_le_pow_right hpos (by omega))
  have hbound : x.n ^ κ ≤ (x.n + 1) ^ r :=
    (Nat.pow_le_pow_left (by omega) κ).trans (Nat.pow_le_pow_right hpos (by omega))
  have hsize : x.n + 1 ≤ (x.n + 1) ^ r := Nat.le_self_pow (by omega) _
  have hfr := w.fr_le x
  rw [← hU] at hneed hbound
  -- `X` bounds the parts that do not come from the solver, `Z ≥ X` those that do
  have hXZ : (x.n + 1) ^ r ≤ 2 ^ (s + k) * (x.n + 1) ^ r := Nat.le_mul_of_pos_left _ (by positivity)
  have hgoal : polyBound (s + k + 5 + Nat.size w.cst) r [x.n] =
      32 * (2 ^ Nat.size w.cst * (2 ^ (s + k) * (x.n + 1) ^ r)) := by
    unfold polyBound
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add 2 (s + k + 5) (Nat.size w.cst), pow_add 2 (s + k) 5]
    ring
  generalize 2 ^ (s + k) * (x.n + 1) ^ r = Z at *
  generalize (x.n + 1) ^ r = X at *
  -- `Y ≥ Z` takes in the constant of the layout
  have hcst : w.cst * (x.n * x.n + 1) ≤ 2 ^ Nat.size w.cst * Z :=
    Nat.mul_le_mul (Nat.lt_size_self w.cst).le (hsquare.trans hXZ)
  have hZY : Z ≤ 2 ^ Nat.size w.cst * Z := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  generalize 2 ^ Nat.size w.cst * Z = Y at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [limits, hgoal] <;> omega
end Light.Wrap
