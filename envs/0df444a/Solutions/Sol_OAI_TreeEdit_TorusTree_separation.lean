-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:50:48.231334+00:00
-- url     : https://prove2.me/submissions/12011312-7b95-4542-9af2-5177e6c26c04

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleSeparation.lean:L103-L177
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Theorems.Thm_OAI_TreeEdit_Words_cycles_deficit

-- ---- from OAI.Combinatorics.TreeEdit.CyclicWords ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace Words

variable {β : Type*} {n : ℕ}

end Words

lemma deficit_singleton {β : Type*} {x y : β} (hxy : x ≠ y) : deficit [x] [y] = 1 := by
  obtain ⟨z, hz1, hz2, hz⟩ := exists_lcs [x] [y]
  have he : z = [] := by
    rcases List.sublist_singleton.mp hz1 with he | he
    · exact he
    · subst z
      simp [List.sublist_singleton, hxy] at hz2
  have hl : lcs [x] [y] = 0 := by simpa [he] using hz.symm
  simp [deficit, hl]

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.TreeArithmetic ----
namespace OAI

namespace TreeEdit.FiniteTree

universe u

attribute [local instance] Classical.propDecidable

lemma length_eq (m T h : ℕ) : length m T h = (m * T) ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [length, ih, pow_succ]; ring

end TreeEdit.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma point_period {n : ℕ} (hn : 0 < n) : n • point n = 0 := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
  exact AddCircle.coe_period (1 : ℝ)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleSeparation ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma representative_coe (t : UnitAddCircle) : (representative t : UnitAddCircle) = t :=
  AddCircle.coe_equivIco

lemma bin_equal_close {R : ℕ} [NeZero R] {x y : UnitAddCircle} (hxy : bin R x = bin R y) :
    ‖y - x‖ < (R : ℝ)⁻¹ := by
  have he : ⌊(R : ℝ) * representative x⌋₊ = ⌊(R : ℝ) * representative y⌋₊ := congrArg Fin.val hxy
  have hxlo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg R) (representative_mem x).1)
  have hylo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg R) (representative_mem y).1)
  have hxhi := Nat.lt_floor_add_one ((R : ℝ) * representative x)
  have hyhi := Nat.lt_floor_add_one ((R : ℝ) * representative y)
  rw [he] at hxlo hxhi
  have hr : (0 : ℝ) < R := by exact_mod_cast NeZero.pos R
  have ha : |representative y - representative x| < (R : ℝ)⁻¹ := by
    apply (mul_lt_mul_iff_right₀ hr).mp
    rw [mul_inv_cancel₀ hr.ne', ← abs_of_pos hr, ← abs_mul, abs_lt]
    constructor <;> nlinarith
  calc
    ‖y - x‖ = ‖((representative y - representative x : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub, representative_coe, representative_coe]
    _ ≤ |representative y - representative x| := QuotientAddGroup.norm_mk_le_norm
    _ < _ := ha

lemma good_children_int {I : Type} {g s L h : ℕ} {ε : ℝ} {r : I → ℕ} {j : Fin g → I}
    (hr : ∀ i, 0 < r i) {C : Config I L (g * s) (h + 1)} {t : UnitAddCircle}
    (ht : Good ε r j (h + 1) C t) (a : ℤ) :
    g * s ≤ 64 * (Finset.univ.filter (fun i : Fin (g * s) => Good ε r j h (C.2 i).2
      (t + a • ((coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1))))).card := by
  let P := period r j C.1
  have hP : 0 < P := period_pos hr j C.1
  let b : Fin P := ⟨(a % (P : ℤ)).toNat, by
    have hz := Int.emod_nonneg a (by exact_mod_cast hP.ne' : (P : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos a (by exact_mod_cast hP : (0 : ℤ) < P)
    exact (Int.toNat_lt_of_ne_zero hP.ne').mpr hl⟩
  have he (c : ℕ) : a • (c • point P) = (b.val * c) • point P := by
    have hz : P • (c • point P) = 0 := by rw [smul_comm, point_period hP, smul_zero]
    have hae : a • (c • point P) = (a % (P : ℤ)) • (c • point P) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv a (P : ℤ)]
      rw [add_zsmul, mul_comm (P : ℤ), mul_smul, Nat.cast_smul_eq_nsmul ℤ, hz, smul_zero, add_zero]
    rw [hae]
    have hb : (b.val : ℤ) = a % (P : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hP.ne'))
    rw [← hb, Nat.cast_smul_eq_nsmul ℤ, ← mul_smul]
  dsimp [P] at he
  simp_rw [he]
  exact ht b

theorem separation {I : Type} {g s L T R h : ℕ} [NeZero R]
    {r : I → ℕ} {j : Fin g → I} (hr : ∀ i, 0 < r i) (hm : 4 ≤ g * s) (hT : 0 < T)
    (C : Config I L (g * s) h) (x : State UnitAddCircle (g * s) h) (t : UnitAddCircle)
    (ht : Good (R : ℝ)⁻¹ r j h C t) :
    (FiniteTree.length (g * s) T h : ℝ) ≤ (128 : ℝ) ^ h *
      (deficit (word r j T R h C x).val (word r j T R h C (x + diagonal (A := UnitAddCircle) (m := g * s) h t)).val : ℝ) := by
  induction h generalizing t with
  | zero =>
    have hne : bin R x ≠ bin R (x + t) := by
      intro he
      have hh := bin_equal_close he
      rw [add_sub_cancel_left] at hh
      exact hh.not_ge ht
    have hw (z : State UnitAddCircle (g * s) 0) : (word r j T R 0 C z).val = [bin R z] := by
      change List.ofFn (fun _ : Fin 1 => bin R z) = _
      simp [List.ofFn_succ]
    rw [hw x, hw (x + diagonal (A := UnitAddCircle) (m := g * s) 0 t)]
    change _ ≤ _ * (deficit [bin R x] [bin R (x + t)] : ℝ)
    rw [deficit_singleton hne]
    norm_num [FiniteTree.length]
  | succ h ih =>
    let m := g * s
    let B := FiniteTree.length m T h
    have hB : 0 < B := by dsimp [B]; rw [FiniteTree.length_eq]; positivity
    let X (a : Fin T) (i : Fin m) := word r j T R h (C.2 i).2
      (x i + diagonal (A := UnitAddCircle) (m := g * s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))
    let Y (a : Fin T) (i : Fin m) := word r j T R h (C.2 i).2
      ((x + diagonal (A := UnitAddCircle) (m := g * s) (h + 1) t) i + diagonal (A := UnitAddCircle) (m := g * s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))
    let δ : ℝ := (m : ℝ) * B / (64 * (128 : ℝ) ^ h)
    have hpow : 0 < (128 : ℝ) ^ h := by positivity
    have hpow1 : 1 ≤ (128 : ℝ) ^ h := one_le_pow₀ (by norm_num)
    have hδ : δ ≤ ((m - 2) * B : ℕ) := by
      have hm2 : (m : ℝ) ≤ 2 * (m - 2 : ℕ) := by exact_mod_cast (show m ≤ 2 * (m - 2) by omega)
      dsimp [δ]
      rw [div_le_iff₀ (by positivity)]
      push_cast
      nlinarith [(Nat.cast_nonneg (m - 2) : (0 : ℝ) ≤ (m - 2 : ℕ)), (Nat.cast_nonneg B : (0 : ℝ) ≤ B),
        mul_le_mul_of_nonneg_right hm2 (Nat.cast_nonneg B),
        mul_nonneg (show (0 : ℝ) ≤ (m - 2 : ℕ) * B by positivity) (show (0 : ℝ) ≤ 128 ^ h - 1 by linarith)]
    have hblocks (a b : Fin T) : δ ≤ ∑ i : Fin m, (deficit (X a i).val (Y b i).val : ℝ) := by
      let d : ℤ := (b.val : ℤ) - a.val
      let good := Finset.univ.filter (fun i : Fin m => Good (R : ℝ)⁻¹ r j h (C.2 i).2
        (t + d • ((coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1))))
      have hg : m ≤ 64 * good.card := good_children_int hr ht d
      have hlocal (i : Fin m) (hi : i ∈ good) :
          (B : ℝ) ≤ (128 : ℝ) ^ h * (deficit (X a i).val (Y b i).val : ℝ) := by
        have hh := ih (C.2 i).2
          (x i + diagonal (A := UnitAddCircle) (m := g * s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)))
          _ (Finset.mem_filter.mp hi).2
        have he : (x + diagonal (A := UnitAddCircle) (m := g * s) (h + 1) t) i + diagonal (A := UnitAddCircle) (m := g * s) h ((b.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)) =
            (x i + diagonal (A := UnitAddCircle) (m := g * s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1))) +
              diagonal (A := UnitAddCircle) (m := g * s) h (t + d • ((coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1))) := by
          change x i + diagonal (A := UnitAddCircle) (m := g * s) h t + _ = _
          simp only [d, sub_zsmul, Nat.cast_smul_eq_nsmul ℤ, mul_smul, map_add, map_neg, map_nsmul]
          abel
        simpa only [X, Y, he] using hh
      have hsum := Finset.sum_le_sum (s := good) hlocal
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
      have hsub : (∑ i ∈ good, (deficit (X a i).val (Y b i).val : ℝ)) ≤
          ∑ i : Fin m, (deficit (X a i).val (Y b i).val : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
      have hg' : (m : ℝ) ≤ 64 * good.card := by exact_mod_cast hg
      apply (div_le_iff₀ (by positivity : 0 < 64 * (128 : ℝ) ^ h)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hg' (Nat.cast_nonneg B),
        mul_le_mul_of_nonneg_left hsub hpow.le]
    have hh := Words.cycles_deficit (by omega : 2 ≤ m) hB X Y δ hδ hblocks
    change (T : ℝ) * δ ≤ 2 * (deficit (word r j T R (h + 1) C x).val
      (word r j T R (h + 1) C (x + diagonal (A := UnitAddCircle) (m := g * s) (h + 1) t)).val : ℝ) at hh
    have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 64 * (128 : ℝ) ^ h)
    dsimp [δ] at hh'
    rw [mul_assoc, div_mul_cancel₀ _ (by positivity : (64 * (128 : ℝ) ^ h) ≠ 0)] at hh'
    simp only [FiniteTree.length, Nat.cast_mul, pow_succ]
    dsimp [m, B] at hh'
    push_cast at hh'
    nlinarith only [hh']

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.separation := @_root_.OAI.TreeEdit.TorusTree.separation
