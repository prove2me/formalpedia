-- Prove2me | solution 1 for OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T14:02:32.020994+00:00
-- url     : https://prove2.me/submissions/7da0f40b-f4ec-4b0e-b783-16de88bae4b2

import Mathlib
import Definitions.Def_OAIQWSLT000

section
-- module Solutions.OAIQW_LiebThirring.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.CubeFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u37 u38

/-! Equivariant cubical barycentric flags. A codimension-one face of a full
flag has one canonical neighboring flag; this avoids any orientation choices. -/
noncomputable section
open Finset
namespace SharpLiebThirring.CubeFlags

lemma Flag.vertex_bounds {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) :
    2 * F.base i ≤ F.vertex k i ∧ F.vertex k i ≤ 2 * F.base i + 2 := by
  simp only [vertex]
  split_ifs <;> omega

lemma Flag.point_bounds {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) :
    (F.base i : ℝ) ≤ F.point k i ∧ F.point k i ≤ F.base i + 1 := by
  obtain ⟨h₁, h₂⟩ := F.vertex_bounds k i
  have h₁r : (2 : ℝ) * F.base i ≤ F.vertex k i := by exact_mod_cast h₁
  have h₂r : (F.vertex k i : ℝ) ≤ 2 * F.base i + 2 := by exact_mod_cast h₂
  dsimp [point]
  constructor <;> linarith

lemma Flag.flip_flip {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).flip i = F := by
  ext j <;> simp [flip]

lemma Flag.cross_cross {n : ℕ} (F : Flag n) (i : Fin n) : (F.cross i).cross i = F := by
  ext j <;> simp [cross, flip, Function.update_apply]
  split_ifs <;> simp_all

lemma Flag.swap_swap {n : ℕ} (F : Flag n) (i j : Fin n) :
    (F.swap i j).swap i j = F := by
  ext k <;> simp [swap]

lemma Flag.flip_vertex {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1))
    (hik : (F.order.symm i).val < k.val) : (F.flip i).vertex k = F.vertex k := by
  funext j
  by_cases hj : j = i
  · subst j; simp [vertex, flip, hik]
  · simp [vertex, flip, Function.update_of_ne hj]

lemma Flag.cross_vertex {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1))
    (hik : k.val ≤ (F.order.symm i).val) : (F.cross i).vertex k = F.vertex k := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [vertex, cross, flip, Function.update_self]
    have h : ¬ (F.order.symm i).val < k.val := by omega
    simp only [h, ↓reduceIte]
    cases F.corner i <;> norm_num <;> ring
  · simp [vertex, cross, flip, Function.update_of_ne hj]

lemma Flag.swap_vertex {n : ℕ} (F : Flag n) (i j : Fin n) (k : Fin (n + 1))
    (hik : i.val < k.val ↔ j.val < k.val) : (F.swap i j).vertex k = F.vertex k := by
  funext a
  simp only [vertex, swap, Equiv.symm_trans, Equiv.symm_swap, Equiv.trans_apply]
  congr 1
  have h : ((Equiv.swap i j) (F.order.symm a)).val < k.val ↔ (F.order.symm a).val < k.val := by
    by_cases hi : F.order.symm a = i
    · simp [hi, hik]
    by_cases hj : F.order.symm a = j
    · simp [hj, hik]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  simp only [h]
  split_ifs <;> simp_all

lemma Flag.neighbor_neighbor {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) :
    (F.neighbor j).neighbor j = F := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀, flip_order]
    exact flip_flip F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ, cross_order]
    exact cross_cross F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    exact swap_swap F _ _

lemma Flag.neighbor_vertex {n : ℕ} [NeZero n] (F : Flag n) (j k : Fin (n + 1))
    (hjk : k ≠ j) : (F.neighbor j).vertex k = F.vertex k := by
  have hval : k.val ≠ j.val := fun h ↦ hjk (Fin.ext h)
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀]
    apply flip_vertex
    simp only [Equiv.symm_apply_apply]
    omega
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ]
    apply cross_vertex
    simp only [Equiv.symm_apply_apply]
    omega
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    apply swap_vertex
    simp only
    omega

lemma Flag.flip_ne {n : ℕ} (F : Flag n) (i : Fin n) : F.flip i ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.corner i) he
  simp only [flip, Function.update_self] at h
  exact (Bool.not_eq_self (F.corner i)).mp h

lemma Flag.cross_ne {n : ℕ} (F : Flag n) (i : Fin n) : F.cross i ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.base i) he
  simp only [cross, Function.update_self] at h
  split_ifs at h <;> omega

lemma Flag.swap_ne {n : ℕ} (F : Flag n) (i j : Fin n) (hij : i ≠ j) : F.swap i j ≠ F := by
  intro he
  have h := congrArg (fun G : Flag n ↦ G.order i) he
  simp only [swap, Equiv.trans_apply, Equiv.swap_apply_left] at h
  exact hij (F.order.injective h).symm

lemma Flag.neighbor_ne {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) :
    F.neighbor j ≠ F := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀]
    exact flip_ne F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ]
    exact cross_ne F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    apply swap_ne
    intro h
    have hf := congrArg Fin.val h
    simp only at hf
    omega

lemma Flag.reflect_flip {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i : Fin n) :
    (F.flip i).reflect s = (F.reflect s).flip i := by
  ext j <;> simp only [reflect, flip]
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    cases s i <;> cases F.corner i <;> rfl
  · simp [Function.update_of_ne hji]

lemma Flag.reflect_cross {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i : Fin n) :
    (F.cross i).reflect s = (F.reflect s).cross i := by
  ext j <;> simp only [reflect, cross, flip]
  · by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
        rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
        simp [hs, hc]
      omega
    · simp [Function.update_of_ne hji]
  · by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      cases s i <;> cases F.corner i <;> rfl
    · simp [Function.update_of_ne hji]

lemma Flag.reflect_swap {n : ℕ} (s : Fin n → Bool) (F : Flag n) (i j : Fin n) :
    (F.swap i j).reflect s = (F.reflect s).swap i j := rfl

lemma Flag.reflect_neighbor {n : ℕ} [NeZero n] (s : Fin n → Bool)
    (F : Flag n) (j : Fin (n + 1)) :
    (F.neighbor j).reflect s = (F.reflect s).neighbor j := by
  by_cases h₀ : j.val = 0
  · simp only [neighbor, dite_eq_left h₀, reflect]
    exact reflect_flip s F _
  by_cases hₙ : j.val = n
  · simp only [neighbor, dite_eq_right h₀, dite_eq_left hₙ, reflect]
    exact reflect_cross s F _
  · simp only [neighbor, dite_eq_right h₀, dite_eq_right hₙ]
    exact reflect_swap s F _ _

lemma Flag.smul_def {n : ℕ} (s : Signs n) (F : Flag n) : s • F = F.reflect s.val := rfl

lemma Flag.smul_neighbor {n : ℕ} [NeZero n] (s : Signs n)
    (F : Flag n) (j : Fin (n + 1)) :
    s • F.neighbor j = (s • F).neighbor j := F.reflect_neighbor s.val j

lemma Flag.depth_point {n : ℕ} (F : Flag n) (i : Fin n) (k : Fin (n + 1)) :
    F.depth i (F.point k) = if (F.order.symm i).val < k.val then 1 / 2 else 0 := by
  simp only [depth, point, vertex]
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat] <;> split_ifs <;> norm_num <;> ring

lemma Flag.depth_combination {n : ℕ} (F : Flag n) (i : Fin n)
    {ι : Type u38} [Fintype ι] (w : ι → ℝ) (x : ι → Fin n → ℝ) (hw : ∑ k, w k = 1) :
    F.depth i (∑ k, w k • x k) = ∑ k, w k * F.depth i (x k) := by
  simp only [depth, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw, one_mul]

lemma Flag.depth_nonneg {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    0 ≤ F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs]
  apply Finset.sum_nonneg
  intro k _
  have hk := hw k
  rw [F.depth_point]
  split_ifs <;> positivity

lemma Flag.depth_le_half {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    F.depth i (∑ k, w k • F.point k) ≤ 1 / 2 := by
  rw [F.depth_combination i w F.point hs]
  calc
    _ ≤ ∑ k, w k * (1 / 2) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (hw k)
      rw [F.depth_point]
      split_ifs <;> norm_num
    _ = 1 / 2 := by rw [← Finset.sum_mul, hs, one_mul]

lemma Flag.depth_antitone {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i j : Fin n) (hij : F.order.symm i ≤ F.order.symm j) :
    F.depth j (∑ k, w k • F.point k) ≤ F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs, F.depth_combination j w F.point hs]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _ (hw k)
  rw [F.depth_point, F.depth_point]
  split_ifs <;> try norm_num
  exact False.elim (by omega)

lemma Flag.combination_bounds {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    (F.base i : ℝ) ≤ (∑ k, w k • F.point k) i ∧
      (∑ k, w k • F.point k) i ≤ F.base i + 1 := by
  have h₀ := F.depth_nonneg w hw hs i
  have h₁ := F.depth_le_half w hw hs i
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
    constructor <;> linarith


/-- The corner vertex controls strict distance from the midplanes. -/
lemma Flag.depth_lt_half_of_pos_zero {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (h₀ : 0 < w 0)
    (hs : ∑ k, w k = 1) (i : Fin n) :
    F.depth i (∑ k, w k • F.point k) < 1 / 2 := by
  rw [F.depth_combination i w F.point hs]
  calc
    _ < ∑ k, w k * (1 / 2) := by
      apply Finset.sum_lt_sum
      · intro k _
        apply mul_le_mul_of_nonneg_left _ (hw k)
        rw [F.depth_point]
        split_ifs <;> norm_num
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        rw [F.depth_point]
        simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, mul_zero]
        exact mul_pos h₀ (by norm_num)
    _ = 1 / 2 := by rw [← Finset.sum_mul, hs, one_mul]

lemma Flag.depth_pos_of_weight {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i : Fin n) (k : Fin (n + 1)) (hk : (F.order.symm i).val < k.val) (hkw : 0 < w k) :
    0 < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs]
  apply Finset.sum_pos'
  · intro l _
    have hl := hw l
    rw [F.depth_point]
    split_ifs <;> positivity
  · refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [F.depth_point, ite_eq_left hk]
    exact mul_pos hkw (by norm_num)

lemma Flag.depth_strictAnti_of_weight {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (i j : Fin n) (hij : F.order.symm i < F.order.symm j)
    (hpos : 0 < w (F.order.symm i).succ) :
    F.depth j (∑ k, w k • F.point k) < F.depth i (∑ k, w k • F.point k) := by
  rw [F.depth_combination i w F.point hs, F.depth_combination j w F.point hs]
  apply Finset.sum_lt_sum
  · intro k _
    apply mul_le_mul_of_nonneg_left _ (hw k)
    rw [F.depth_point, F.depth_point]
    split_ifs <;> try norm_num
    exact False.elim (by omega)
  · refine ⟨(F.order.symm i).succ, Finset.mem_univ _, ?_⟩
    rw [F.depth_point, F.depth_point]
    simp only [Fin.val_succ]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    nlinarith

/-- Bottom-facet interiors are disjoint among flags on the same side of the
bottom hyperplane. The last coordinate expanded is the time coordinate `t`. -/
lemma Flag.eq_of_facet_combination {n : ℕ} [NeZero n] (F G : Flag n)
    (t : Fin n) (ht : (F.order.symm t).val = n - 1)
    (hbt : F.base t = G.base t) (hct : F.corner t = G.corner t)
    (w z : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hwp : ∀ k, k ≠ Fin.last n → 0 < w k) (hz : ∀ k, 0 ≤ z k)
    (hsw : ∑ k, w k = 1) (hsz : ∑ k, z k = 1)
    (he : ∑ k, w k • F.point k = ∑ k, z k • G.point k) : F = G := by
  have hn : n ≠ 0 := NeZero.ne n
  have hw₀ : 0 < w 0 := hwp 0 (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)
  have hdep (i : Fin n) (hi : i ≠ t) : 0 < F.depth i (∑ k, w k • F.point k) := by
    have hp : (F.order.symm i).val < n - 1 := by
      have hne : F.order.symm i ≠ F.order.symm t := fun h ↦ hi (F.order.symm.injective h)
      have hval : (F.order.symm i).val ≠ (F.order.symm t).val := fun h ↦ hne (Fin.ext h)
      have := (F.order.symm i).isLt
      omega
    apply F.depth_pos_of_weight w hw hsw i (F.order.symm i).succ (by simp)
    apply hwp
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_last] at hv
    omega
  have hb : F.base = G.base := by
    funext i
    by_cases hi : i = t
    · simpa only [hi] using hbt
    have h₀ := hdep i hi
    have h₁ := F.depth_lt_half_of_pos_zero w hw hw₀ hsw i
    have hF : (F.base i : ℝ) < (∑ k, w k • F.point k) i ∧
        (∑ k, w k • F.point k) i < F.base i + 1 := by
      rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
        simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
        constructor <;> linarith
    have hG := G.combination_bounds z hz hsz i
    rw [← he] at hG
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc : (F.base i : ℝ) + 1 ≤ G.base i := by
        exact_mod_cast (show F.base i + 1 ≤ G.base i by omega)
      linarith
    · have hc : (G.base i : ℝ) + 1 ≤ F.base i := by
        exact_mod_cast (show G.base i + 1 ≤ F.base i by omega)
      linarith
  have hc : F.corner = G.corner := by
    funext i
    by_cases hi : i = t
    · simpa only [hi] using hct
    have hF := F.depth_lt_half_of_pos_zero w hw hw₀ hsw i
    have hG := G.depth_le_half z hz hsz i
    rw [← he] at hG
    cases hf : F.corner i <;> cases hg : G.corner i <;> try rfl
    all_goals
      simp only [depth, ← hb, hf, hg, Bool.false_eq_true, ↓reduceIte] at hF hG
      linarith
  have hd (i : Fin n) (x : Fin n → ℝ) : F.depth i x = G.depth i x := by
    simp only [depth, hb, hc]
  have hm : StrictMono (fun i : Fin n ↦ G.order.symm (F.order i)) := by
    intro i j hij
    by_contra hnot
    have hle : G.order.symm (F.order j) ≤ G.order.symm (F.order i) := le_of_not_gt hnot
    have hG := G.depth_antitone z hz hsz (F.order j) (F.order i) hle
    have hF := F.depth_strictAnti_of_weight w hw hsw (F.order i) (F.order j)
      (by simpa using hij) (by
        apply hwp
        intro h
        have hh := congrArg Fin.val h
        simp only [Equiv.symm_apply_apply, Fin.val_succ, Fin.val_last] at hh
        have := j.isLt
        have : i.val < j.val := hij
        omega)
    rw [← he, ← hd, ← hd] at hG
    linarith
  have ho : F.order = G.order := by
    ext i
    have hh := congrFun hm.eq_id i
    have ha := congrArg G.order hh
    exact congrArg Fin.val (by simpa only [Equiv.apply_symm_apply, id_eq] using ha)
  exact Flag.ext hb hc ho

/-- A shared facet whose vertices have trivial stabilizers cannot identify its
two incident flags under a reflection action. The hypothesis will be supplied
by the positive distance from zero-row strata. -/
lemma Flag.neighbor_ne_reflect_of_free {n : ℕ} [NeZero n] (F : Flag n)
    (j : Fin (n + 1)) (s : Signs n)
    (hfree : ∀ k : Fin (n + 1),
      (∀ i, (if s.val i then -F.vertex k i else F.vertex k i) = F.vertex k i) → s = 1) :
    F.neighbor j ≠ s • F := by
  intro he
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ j := by
    by_cases hj : j.val = 0
    · exact ⟨⟨n, by omega⟩, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
    · exact ⟨0, by intro h; have hh := congrArg Fin.val h; simp at hh; omega⟩
  have hs : s = 1 := by
    apply hfree k
    intro i
    have hv := congrArg (fun G : Flag n ↦ G.vertex k i) he
    rw [F.neighbor_vertex j k hk] at hv
    simpa only [smul_def, reflect_vertex] using hv.symm
  rw [hs, one_smul] at he
  exact F.neighbor_ne j he

end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlagGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u39

noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags

lemma Signs.smul_real {n : ℕ} (s : Signs n) (x : Fin n → ℝ) (i : Fin n) :
    (s • x) i = if s.val i then -x i else x i := rfl

lemma Signs.smul_int {n : ℕ} (s : Signs n) (x : Fin n → ℤ) (i : Fin n) :
    (s • x) i = if s.val i then -x i else x i := rfl

lemma Flag.dist_point_center {n : ℕ} (F : Flag n) (k : Fin (n + 1)) :
    dist (F.point k) F.center ≤ 1 / 2 := by
  rw [dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  intro i
  rw [Real.dist_eq, abs_le, F.center_apply]
  have hb := F.point_bounds k i
  constructor <;> linarith

lemma Flag.dist_combination_center {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    dist (∑ k, w k • F.point k) F.center ≤ 1 / 2 := by
  rw [dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  intro i
  rw [Real.dist_eq, abs_le, F.center_apply]
  have hb := F.combination_bounds w hw hs i
  constructor <;> linarith

lemma Flag.dist_combination_point {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (∑ l, w l • F.point l) (F.point k) ≤ 1 := by
  calc
    _ ≤ dist (∑ l, w l • F.point l) F.center + dist F.center (F.point k) := dist_triangle _ _ _
    _ ≤ 1 / 2 + 1 / 2 := add_le_add (F.dist_combination_center w hw hs)
      (by rw [dist_comm]; exact F.dist_point_center k)
    _ = 1 := by norm_num

lemma dist_scale {E : Type u39} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (hh : 0 ≤ h) (x y : E) : dist (h • x) (h • y) = h * dist x y := by
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

lemma Flag.dist_scaled_point_center {n : ℕ} (F : Flag n) (h : ℝ) (hh : 0 ≤ h)
    (k : Fin (n + 1)) : dist (h • F.point k) (h • F.center) ≤ h / 2 := by
  rw [dist_scale h hh]
  nlinarith [F.dist_point_center k]

lemma Flag.point_time_boundary {n : ℕ} [NeZero n] (F : Flag n) (t : Fin n)
    (ht : (F.order.symm t).val = n - 1) (k : Fin (n + 1)) (hk : k ≠ Fin.last n) :
    F.point k t = (F.base t : ℝ) + if F.corner t then 1 else 0 := by
  have hp : 0 < n := NeZero.pos n
  have hk' : k.val < n := by
    have hh : k.val ≠ n := fun h ↦ hk (Fin.ext h)
    omega
  simp only [point, vertex, ht, show ¬ n - 1 < k.val by omega, ↓reduceIte]
  rcases Bool.eq_false_or_eq_true (F.corner t) with hc | hc <;> simp [hc]
  ring

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags

lemma gridPoint_vertex {n : ℕ} (h : ℝ) (F : Flag n) (k : Fin (n + 1)) :
    gridPoint h (F.vertex k) = h • F.point k := by
  ext i
  simp only [gridPoint, Pi.smul_apply, smul_eq_mul, Flag.point]
  ring

lemma gridPoint_smul {n : ℕ} (h : ℝ) (s : Signs n) (z : Fin n → ℤ) :
    gridPoint h (s • z) = s • gridPoint h z := by
  ext i
  simp only [gridPoint, Signs.smul_real, Signs.smul_int]
  rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  ring

end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FiniteParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60 u61 u62 u63 u64 u65 u66 u67

noncomputable section
open Finset


/-! Finite parity for the PL continuation argument.
The argument constructs continuation without assuming a topological degree theorem. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity

/-- Endpoints of a line meeting a simplex: in general position either no facet,
or exactly two facets, are met. The roots `r` are the facet crossing parameters. -/
lemma affine_constraints_endpoints {ι : Type u40} [Fintype ι] [DecidableEq ι]
    (b r : ι → ℝ) (hb : ∀ i, b i ≠ 0) (hr : Function.Injective r)
    (hpos : ∃ i, 0 < b i) (hneg : ∃ i, b i < 0) :
    ∃ i j : ι, i ≠ j ∧
      ({k | ∀ l, 0 ≤ b l * (r k - r l)} : Finset ι) =
        if r i < r j then {i, j} else ∅ := by
  classical
  have hp : (univ.filter (fun i ↦ 0 < b i)).Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [hi]⟩
  have hn : (univ.filter (fun i ↦ b i < 0)).Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, by simp [hi]⟩
  obtain ⟨i, hi, hmax⟩ := exists_max_image (univ.filter (fun i ↦ 0 < b i)) r hp
  obtain ⟨j, hj, hmin⟩ := exists_min_image (univ.filter (fun i ↦ b i < 0)) r hn
  simp only [mem_filter, mem_univ, true_and] at hi hj hmax hmin
  have hij : i ≠ j := by rintro rfl; linarith
  have hrij : r i ≠ r j := fun h ↦ hij (hr h)
  refine ⟨i, j, hij, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and]
  by_cases hlt : r i < r j
  · rw [ite_eq_left hlt]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hk
      have hleft : r i ≤ r k := by
        have hh := (mul_nonneg_iff_of_pos_left hi).mp (hk i)
        linarith
      have hright : r k ≤ r j := by
        have hh := nonpos_of_mul_nonneg_right (hk j) hj
        linarith
      rcases lt_or_gt_of_ne (hb k) with hkn | hkp
      · right
        have hh := hmin k hkn
        exact hr (le_antisymm hright hh)
      · left
        have hh := hmax k hkp
        exact hr (le_antisymm hh hleft)
    · rintro (rfl | rfl) l
      · rcases lt_or_gt_of_ne (hb l) with hln | hlp
        · apply mul_nonneg_of_nonpos_of_nonpos hln.le
          have hh := hmin l hln
          linarith
        · exact mul_nonneg hlp.le (sub_nonneg.mpr (hmax l hlp))
      · rcases lt_or_gt_of_ne (hb l) with hln | hlp
        · exact mul_nonneg_of_nonpos_of_nonpos hln.le (sub_nonpos.mpr (hmin l hln))
        · apply mul_nonneg hlp.le
          have hh := hmax l hlp
          linarith
  · rw [ite_eq_right hlt]
    simp only [Finset.notMem_empty, iff_false]
    intro hk
    have hleft : r i ≤ r k := by
      have hh := (mul_nonneg_iff_of_pos_left hi).mp (hk i)
      linarith
    have hright : r k ≤ r j := by
      have hh := nonpos_of_mul_nonneg_right (hk j) hj
      linarith
    exact hrij (le_antisymm (hleft.trans hright) (le_of_not_gt hlt))

lemma even_affine_constraints_endpoints {ι : Type u41} [Fintype ι] [DecidableEq ι]
    (b r : ι → ℝ) (hb : ∀ i, b i ≠ 0) (hr : Function.Injective r)
    (hpos : ∃ i, 0 < b i) (hneg : ∃ i, b i < 0) :
    Even ({k | ∀ l, 0 ≤ b l * (r k - r l)} : Finset ι).card := by
  obtain ⟨i, j, hij, he⟩ := affine_constraints_endpoints b r hb hr hpos hneg
  rw [he]
  split_ifs <;> simp [hij]


section AffineFiber
attribute [local instance] Classical.propDecidable
variable {ι : Type u42} {V : Type u43} [Fintype ι]
  [AddCommGroup V] [Module ℝ V]

lemma facetHit_congr (v u : ι → V) (i : ι) (he : ∀ j, j ≠ i → v j = u j) :
    facetHit v i ↔ facetHit u i := by
  have hs (w : ι → ℝ) (hw : w i = 0) : ∑ j, w j • v j = ∑ j, w j • u j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · simp only [hji, hw, zero_smul]
    · rw [he j hji]
  constructor <;> rintro ⟨w, hw, hi, hn⟩ <;> refine ⟨w, ?_, hi, hn⟩
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • u j = 0
      rw [← hs w hi]
      exact congrArg Prod.snd hw
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • v j = 0
      rw [hs w hi]
      exact congrArg Prod.snd hw

lemma kernel_line_parameterization (v : ι → V)
    (hdim : Module.finrank ℝ (LinearMap.ker (augmentedMap v)) = 1)
    {b : ι → ℝ} (hb : b ∈ LinearMap.ker (augmentedMap v)) (hb0 : b ≠ 0)
    {a w : ι → ℝ} (ha : augmentedMap v a = (1, 0))
    (hw : augmentedMap v w = (1, 0)) :
    ∃ t : ℝ, w = a + t • b := by
  have hwb : w - a ∈ LinearMap.ker (augmentedMap v) := by
    rw [LinearMap.mem_ker, map_sub, hw, ha, sub_self]
  obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hdim
    (x := (⟨b, hb⟩ : LinearMap.ker (augmentedMap v)))
    (by simpa using hb0) (⟨w - a, hwb⟩ : LinearMap.ker (augmentedMap v))
  refine ⟨t, ?_⟩
  have h := congrArg Subtype.val ht
  change t • b = w - a at h
  rw [h, add_sub_cancel]

/-- Parity of facet hits for a generic affine map from a (d+1)-simplex to
R^d. The algebraic general-position conditions are separated from the
finite counting argument so they can be supplied by generic vertex choices. -/
lemma even_facetHit_of_kernel_line (v : ι → V)
    (hsur : Function.Surjective (augmentedMap v))
    (hdim : Module.finrank ℝ (LinearMap.ker (augmentedMap v)) = 1)
    (hcoord : ∀ b : ι → ℝ, augmentedMap v b = 0 → b ≠ 0 → ∀ i, b i ≠ 0)
    (hpair : ∀ w : ι → ℝ, augmentedMap v w = (1, 0) →
      ∀ i j, w i = 0 → w j = 0 → i = j) :
    Even ({i | facetHit v i} : Finset ι).card := by
  classical
  obtain ⟨a, ha⟩ := hsur (1, 0)
  have hkne : LinearMap.ker (augmentedMap v) ≠ ⊥ := by
    intro h
    rw [h] at hdim
    simp at hdim
  obtain ⟨b, hb, hb0⟩ := (LinearMap.ker (augmentedMap v)).ne_bot_iff.mp hkne
  have hbA : augmentedMap v b = 0 := hb
  have hbi := hcoord b hbA hb0
  have hbSum : ∑ i, b i = 0 := congrArg Prod.fst hbA
  have hpos : ∃ i, 0 < b i := by
    by_contra! h
    have hh := (Finset.sum_eq_zero_iff_of_nonpos (by simpa using h)).mp hbSum
    apply hb0
    ext i
    exact hh i (mem_univ i)
  have hneg : ∃ i, b i < 0 := by
    by_contra! h
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (by simpa using h)).mp hbSum
    apply hb0
    ext i
    exact hh i (mem_univ i)
  let r : ι → ℝ := fun i ↦ -a i / b i
  have hroot (i : ι) : a i + r i * b i = 0 := by
    dsimp [r]
    rw [div_mul_cancel₀ _ (hbi i)]
    ring
  have hr : Function.Injective r := by
    intro i j hij
    apply hpair (a + r i • b)
    · rw [map_add, map_smul, hbA, smul_zero, add_zero, ha]
    · exact hroot i
    · change a j + r i * b j = 0
      rw [hij]
      exact hroot j
  have heq : ({i | facetHit v i} : Finset ι) =
      ({i | ∀ j, 0 ≤ b j * (r i - r j)} : Finset ι) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, hwi, hwj⟩
      obtain ⟨t, rfl⟩ := kernel_line_parameterization v hdim hb hb0 ha hw
      have ht : t = r i := by
        change a i + t * b i = 0 at hwi
        apply (mul_right_cancel₀ (hbi i))
        linarith [hroot i]
      subst t
      intro j
      have hj := hwj j
      change 0 ≤ a j + r i * b j at hj
      nlinarith [hroot j]
    · intro hi
      refine ⟨a + r i • b, ?_, hroot i, ?_⟩
      · rw [map_add, map_smul, hbA, smul_zero, add_zero, ha]
      · intro j
        change 0 ≤ a j + r i * b j
        nlinarith [hi j, hroot j]
  rw [heq]
  exact even_affine_constraints_endpoints b r hbi hr hpos hneg


lemma sum_subtype_eq_of_zero {M : Type u44} [AddCommMonoid M]
    (P : ι → Prop) [DecidablePred P] (f : ι → M) (h : ∀ i, ¬ P i → f i = 0) :
    (∑ i : {i // P i}, f i) = ∑ i, f i := by
  have h0 : (∑ i : {i // ¬ P i}, f i) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ h i i.prop)
  simpa only [h0, add_zero] using Fintype.sum_subtype_add_sum_subtype P f

lemma augmentedMap_single (v : ι → V) (i : ι) :
    augmentedMap v (Pi.single i 1) = (1, v i) := by
  classical
  simp [augmentedMap, Pi.single_apply, ite_smul]

lemma augmented_kernel_nonzero_coordinates (v : ι → V)
    (hgen : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
    (b : ι → ℝ) (hb : augmentedMap v b = 0) (hb0 : b ≠ 0) :
    ∀ i, b i ≠ 0 := by
  intro i hi
  have hs : (∑ j : {j // j ≠ i}, b j • ((1 : ℝ), v j)) = 0 := by
    calc
      _ = ∑ j, b j • ((1 : ℝ), v j) := sum_subtype_eq_of_zero (fun j ↦ j ≠ i) (fun j ↦ b j • ((1 : ℝ), v j)) (by
      intro j hj
      have : j = i := by simpa using hj
      simp [this, hi])
      _ = 0 := by
        simpa only [augmentedMap_apply, Prod.smul_mk, smul_eq_mul, mul_one, ← prod_mk_sum] using hb
  have hz := Fintype.linearIndependent_iff.mp (hgen i) (fun j ↦ b j) hs
  apply hb0
  ext j
  by_cases hj : j = i
  · simpa [hj] using hi
  · exact hz ⟨j, hj⟩

lemma augmented_nonzero_two_coordinates (v : ι → V)
    (hgen : ∀ i j : ι, i ≠ j →
      LinearIndependent ℝ (fun k : {k // k ≠ i ∧ k ≠ j} ↦ v k))
    (w : ι → ℝ) (hw : augmentedMap v w = (1, 0))
    (i j : ι) (hi : w i = 0) (hj : w j = 0) : i = j := by
  by_contra hij
  have hs : (∑ k : {k // k ≠ i ∧ k ≠ j}, w k • v k) = 0 := by
    calc
      _ = ∑ k, w k • v k := sum_subtype_eq_of_zero (fun k ↦ k ≠ i ∧ k ≠ j) (fun k ↦ w k • v k) (by
      intro k hk
      by_cases hki : k = i
      · simp [hki, hi]
      · have hkj : k = j := by aesop
        simp [hkj, hj])
      _ = 0 := congrArg Prod.snd hw
  have hz := Fintype.linearIndependent_iff.mp (hgen i j hij) (fun k ↦ w k) hs
  have hw0 : w = 0 := by
    ext k
    by_cases hki : k = i
    · simpa [hki] using hi
    by_cases hkj : k = j
    · simpa [hkj] using hj
    exact hz ⟨k, hki, hkj⟩
  simpa [hw0] using congrArg Prod.fst hw

lemma augmentedMap_surjective [FiniteDimensional ℝ V] (v : ι → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 2)
    (hgen : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j))) :
    Function.Surjective (augmentedMap v) := by
  classical
  have hcpos : 0 < Fintype.card ι := by omega
  let : Nonempty ι := Fintype.card_pos_iff.mp hcpos
  let i : ι := Classical.arbitrary ι
  have hc : Fintype.card {j : ι // j ≠ i} = Module.finrank ℝ (ℝ × V) := by
    rw [Fintype.card_subtype_compl (fun j ↦ j = i)]
    simp [hcard, Module.finrank_prod, Nat.add_comm]
  have hspan : Submodule.span ℝ (Set.range (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
      ≤ LinearMap.range (augmentedMap v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j.val 1, augmentedMap_single v j.val⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  have hs := (hgen i).span_eq_top_of_card_eq_finrank' hc
  rwa [hs] at hspan

lemma even_facetHit [FiniteDimensional ℝ V] (v : ι → V)
    (hcard : Fintype.card ι = Module.finrank ℝ V + 2)
    (haug : ∀ i : ι, LinearIndependent ℝ (fun j : {j // j ≠ i} ↦ ((1 : ℝ), v j)))
    (hvec : ∀ i j : ι, i ≠ j →
      LinearIndependent ℝ (fun k : {k // k ≠ i ∧ k ≠ j} ↦ v k)) :
    Even ({i | facetHit v i} : Finset ι).card := by
  have hsur := augmentedMap_surjective v hcard haug
  apply even_facetHit_of_kernel_line v hsur
  · have hd := LinearMap.finrank_range_add_finrank_ker (augmentedMap v)
    rw [LinearMap.range_eq_top.mpr hsur] at hd
    simp only [finrank_top, Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at hd
    omega
  · exact augmented_kernel_nonzero_coordinates v haug
  · exact augmented_nonzero_two_coordinates v hvec

end AffineFiber
end SharpLiebThirring.PLParity


/-! Free-action double counting for continuation modulo two. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

section OrbitSum
variable {G : Type u45} {X : Type u46} [Group G] [MulAction G X] [IsCancelSMul G X]

lemma sum_eq_card_mul_orbit_sum [Fintype G] [Fintype X]
    (f : X → ℕ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) :
    ∑ x, f x = Fintype.card G * ∑ q : Quotient (MulAction.orbitRel G X), f q.out := by
  classical
  have h := Fintype.sum_equiv (orbitProductEquiv (G := G) (X := X))
    (fun z ↦ f (z.2 • z.1.out)) f (fun _ ↦ rfl)
  rw [← h, Fintype.sum_prod_type]
  simp only [hf, sum_const, card_univ, smul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm
end OrbitSum

section Incidence
variable {G : Type u47} {T : Type u48} {F : Type u49} [Group G] [Fintype G] [Fintype T] [Fintype F]
  [MulAction G T] [MulAction G F] [IsCancelSMul G T] [IsCancelSMul G F]

omit [Fintype G] [Fintype T] [IsCancelSMul G T] [IsCancelSMul G F] in
lemma rowDegree_invariant {R : T → F → Prop}
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f) (g : G) (t : T) :
    rowDegree R (g • t) = rowDegree R t := by
  symm
  exact Fintype.card_congr ((MulAction.toPerm g).subtypeEquiv (fun f ↦ (hR g t f).symm))

omit [Fintype G] [Fintype F] [IsCancelSMul G T] [IsCancelSMul G F] in
lemma colDegree_invariant {R : T → F → Prop}
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f) (g : G) (f : F) :
    colDegree R (g • f) = colDegree R f := by
  symm
  exact Fintype.card_congr ((MulAction.toPerm g).subtypeEquiv (fun t ↦ (hR g t f).symm))

lemma sum_rowDegree_eq_sum_colDegree (R : T → F → Prop) :
    ∑ t, rowDegree R t = ∑ f, colDegree R f := by
  classical
  simp only [rowDegree, colDegree, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  exact Finset.sum_comm

/-- The number of odd-degree facet orbits is even whenever every top-cell
has even degree. This is the equivariant handshaking lemma: the action must
be free, but neither the base nor the target needs an orientation. -/
lemma even_odd_degree_orbits (R : T → F → Prop)
    (hR : ∀ g : G, ∀ t f, R (g • t) (g • f) ↔ R t f)
    (hEven : ∀ t, Even (rowDegree R t)) :
    Even ({q : Quotient (MulAction.orbitRel G F) | Odd (colDegree R q.out)} :
      Finset (Quotient (MulAction.orbitRel G F))).card := by
  classical
  have hsum := sum_rowDegree_eq_sum_colDegree R
  rw [sum_eq_card_mul_orbit_sum (rowDegree R) (rowDegree_invariant hR),
    sum_eq_card_mul_orbit_sum (colDegree R) (colDegree_invariant hR)] at hsum
  have heq := Nat.mul_left_cancel (Fintype.card_pos (α := G)) hsum
  have heven : Even (∑ q : Quotient (MulAction.orbitRel G F), colDegree R q.out) := by
    rw [← heq]
    exact Finset.even_sum _ (fun q _ ↦ hEven q.out)
  exact (Finset.even_sum_iff_even_card_odd _).mp heven

end Incidence
section HalfEdges
variable {G : Type u50} {T : Type u51} {H : Type u52} [Group G] [Fintype G] [Fintype T] [Fintype H]
  [MulAction G T] [MulAction G H] [IsCancelSMul G T] [IsCancelSMul G H]

lemma even_orbit_card_of_even_fibers (p : H → T)
    (hp : ∀ g : G, ∀ h, p (g • h) = g • p h)
    (hEven : ∀ t, Even (Nat.card {h // p h = t})) :
    Even (Fintype.card (Quotient (MulAction.orbitRel G H))) := by
  classical
  have hc (h : H) : colDegree (fun t h ↦ p h = t) h = 1 := by
    simp [colDegree, eq_comm]
  have he := even_odd_degree_orbits (fun t h ↦ p h = t)
    (by intro g t h; rw [hp]; exact smul_left_cancel_iff g)
    (fun t ↦ by simpa only [Nat.card_eq_fintype_card, rowDegree] using hEven t)
  simpa [hc] using he

omit [Fintype G] [Fintype T] [Fintype H] [MulAction G T]
  [IsCancelSMul G T] [IsCancelSMul G H] in
lemma orbitMap_involutive (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    (hi : Function.Involutive f) : Function.Involutive (orbitMap f hf) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
      change Quotient.mk'' (f (f x)) = Quotient.mk'' x
      rw [hi]

lemma even_fixedPoints_of_even_card {X : Type u53} [Fintype X]
    (f : X → X) (hi : Function.Involutive f) (he : Even (Fintype.card X)) :
    Even (Nat.card (Function.fixedPoints f)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  let F : Function.End X := f
  have hf : F ^ (2 : ℕ) ^ (1 : ℕ) = 1 := by
    funext x
    exact hi x
  have hm := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Nat.ModEq] at hm
  exact Nat.even_iff.mpr (hm.symm.trans (Nat.even_iff.mp he))

/-- One initial crossing orbit cannot be the only fixed orbit of an equivariant
half-edge pairing; a second boundary crossing orbit must exist. -/
lemma exists_other_fixed_orbit (p : H → T)
    (hp : ∀ g : G, ∀ h, p (g • h) = g • p h)
    (hEven : ∀ t, Even (Nat.card {h // p h = t}))
    (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    (hi : Function.Involutive f)
    (q₀ : Quotient (MulAction.orbitRel G H)) (hq₀ : orbitMap f hf q₀ = q₀) :
    ∃ q : Quotient (MulAction.orbitRel G H), orbitMap f hf q = q ∧ q ≠ q₀ := by
  classical
  have he := even_fixedPoints_of_even_card (orbitMap f hf) (orbitMap_involutive f hf hi)
    (even_orbit_card_of_even_fibers p hp hEven)
  by_contra! h
  have hsingle : Function.fixedPoints (orbitMap f hf) = {q₀} := by
    ext q
    constructor
    · exact fun hq ↦ h q hq
    · intro hq
      change orbitMap f hf q = q
      simpa [Set.mem_singleton_iff.mp hq] using hq₀
  have hcard : Nat.card (Function.fixedPoints (orbitMap f hf)) = 1 :=
    (Nat.card_congr (Equiv.setCongr hsingle)).trans Nat.card_unique
  rw [hcard] at he
  norm_num at he


end HalfEdges
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.PLParity
namespace FinitePairing
attribute [local instance] Classical.propDecidable

variable {G : Type u64} {X : Type u65} {J : Type u66} [Group G] [MulAction G X]
variable (D : SubMulAction G X)
variable (hit : X → J → Prop) (hHit : ∀ g : G, ∀ x j, hit (g • x) j ↔ hit x j)
variable (nbr : X → J → X)
variable (hInv : ∀ x j, nbr (nbr x j) j = x)
variable (hNbr : ∀ g : G, ∀ x j, nbr (g • x) j = g • nbr x j)
variable (hAdj : ∀ x j, hit x j → hit (nbr x j) j)

lemma pairing_boundary (p : selected D hit hHit)
    (hn : nbr p.val.cell.val p.val.facet ∉ D) :
    pairing D hit hHit nbr hAdj p = p := by
  simp only [pairing, dite_eq_right hn]

include hInv in
lemma pairing_involutive : Function.Involutive (pairing D hit hHit nbr hAdj) := by
  intro p
  by_cases hn : nbr p.val.cell.val p.val.facet ∈ D
  · have hnn : nbr (nbr p.val.cell.val p.val.facet) p.val.facet ∈ D := by
      rw [hInv]; exact p.val.cell.property
    simp only [pairing, dite_eq_left hn, hnn, ↓reduceDIte]
    apply Subtype.ext
    apply CellFacet.ext
    · exact Subtype.ext (hInv _ _)
    · rfl
  · simp only [pairing, dite_eq_right hn]

include hNbr in
lemma pairing_equivariant (g : G) (p : selected D hit hHit) :
    pairing D hit hHit nbr hAdj (g • p) = g • pairing D hit hHit nbr hAdj p := by
  have hg : nbr (g • p.val.cell.val) p.val.facet ∈ D ↔
      nbr p.val.cell.val p.val.facet ∈ D := by
    rw [hNbr]
    exact D.smul_mem_iff' g
  by_cases hn : nbr p.val.cell.val p.val.facet ∈ D
  · have hn' : nbr (g • p).val.cell.val (g • p).val.facet ∈ D := hg.mpr hn
    simp only [pairing, dite_eq_left hn, dite_eq_left hn']
    apply Subtype.ext
    apply CellFacet.ext
    · exact Subtype.ext (hNbr _ _ _)
    · rfl
  · have hn' : nbr (g • p).val.cell.val (g • p).val.facet ∉ D := fun h ↦ hn (hg.mp h)
    simp only [pairing, dite_eq_right hn, dite_eq_right hn']

lemma selected_projection_equivariant (g : G) (p : selected D hit hHit) :
    (g • p).val.cell = g • p.val.cell := rfl

lemma even_projection_fiber [Fintype D] [Fintype J]
    (hEven : ∀ x : D, Even (Nat.card {j // hit x.val j})) (x : D) :
    Even (Nat.card {p : selected D hit hHit // p.val.cell = x}) := by
  let e : {p : selected D hit hHit // p.val.cell = x} ≃ {j // hit x.val j} :=
    { toFun := fun p ↦ ⟨p.val.val.facet, by
        exact (congrArg (fun y : D ↦ hit y.val p.val.val.facet) p.property).mp p.val.property⟩
      invFun := fun j ↦ ⟨⟨⟨x, j.val⟩, j.property⟩, rfl⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply CellFacet.ext
        · exact p.property.symm
        · rfl
      right_inv := fun _ ↦ rfl }
  simpa only [Nat.card_congr e] using hEven x

include hInv hNbr hAdj in
/-- In a free finite equivariant complex with even selected facet counts, a
boundary crossing orbit forces another boundary crossing orbit. -/
lemma exists_other_boundary [Fintype D] [Fintype J] [Fintype G] [IsCancelSMul G X]
    (hEven : ∀ x : D, Even (Nat.card {j // hit x.val j}))
    (hNoOrbit : ∀ x : D, ∀ j, nbr x.val j ∈ D → ∀ g : G, nbr x.val j ≠ g • x.val)
    (p₀ : selected D hit hHit) (hp₀ : nbr p₀.val.cell.val p₀.val.facet ∉ D) :
    ∃ p : selected D hit hHit, nbr p.val.cell.val p.val.facet ∉ D ∧
      ¬ (MulAction.orbitRel G (selected D hit hHit)) p p₀ := by
  let f := pairing D hit hHit nbr hAdj
  have hf := pairing_equivariant D hit hHit nbr hNbr hAdj
  have hi := pairing_involutive D hit hHit nbr hInv hAdj
  let q₀ : Quotient (MulAction.orbitRel G (selected D hit hHit)) := Quotient.mk'' p₀
  have hq₀ : orbitMap f hf q₀ = q₀ := by
    change Quotient.mk'' (f p₀) = Quotient.mk'' p₀
    exact congrArg Quotient.mk'' (pairing_boundary D hit hHit nbr hAdj p₀ hp₀)
  obtain ⟨q, hq, hne⟩ := exists_other_fixed_orbit (fun p : selected D hit hHit ↦ p.val.cell)
    (selected_projection_equivariant D hit hHit)
    (even_projection_fiber D hit hHit hEven) f hf hi q₀ hq₀
  refine ⟨q.out, ?_, ?_⟩
  · intro hin
    have hre : (MulAction.orbitRel G (selected D hit hHit)) (f q.out) q.out := by
      apply Quotient.exact'
      change orbitMap f hf (Quotient.mk'' q.out) = Quotient.mk'' q.out
      simpa only [Quotient.out_eq'] using hq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hre)
    have he := congrArg (fun p : selected D hit hHit ↦ p.val.cell.val) hg
    have hp : (f q.out).val.cell.val = nbr q.out.val.cell.val q.out.val.facet := by
      simp only [f, pairing, dite_eq_left hin]
    rw [hp] at he
    exact hNoOrbit q.out.val.cell q.out.val.facet hin g he.symm
  · intro hr
    apply hne
    exact (Quotient.out_eq' q).symm.trans (Quotient.sound' hr)

end FinitePairing
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open SharpLiebThirring.PLParity
section PLComplex
variable {n : ℕ} [NeZero n] (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
variable {V : Type u67} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V))
attribute [local instance] Classical.propDecidable

omit [NeZero n] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma extendValues_at (a : vertices H D → V) (F : D) (k : Fin (n + 1)) :
    extendValues H D a (F.val.vertex k) = a (flagVertex H D F k) := by
  simp only [extendValues, dite_eq_left (show F.val.vertex k ∈ vertices H D from ⟨F, k, rfl⟩)]
  rfl

omit [FiniteDimensional ℝ V] in
lemma cellHit_neighbor (a : vertices H D → V) (F : Flag n) (j : Fin (n + 1)) :
    cellHit H D a (F.neighbor j) j ↔ cellHit H D a F j := by
  apply facetHit_congr
  intro k hk
  rw [F.neighbor_vertex j k hk]

omit [NeZero n] in
lemma cellHit_even (a : vertices H D → V) (F : D)
    (hc : n = Module.finrank ℝ V + 1)
    (haug : ∀ j : Fin (n + 1), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k))) :
    Even (Nat.card {j // cellHit H D a F.val j}) := by
  have he := even_facetHit (fun k ↦ a (flagVertex H D F k)) (by simpa using hc)
    haug hvec
  simpa only [cellHit, extendValues_at, Nat.card_eq_fintype_card, Fintype.card_subtype] using he

lemma neighbor_not_orbit (h : ℝ) (F : D)
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (j : Fin (n + 1)) (s : H) : F.val.neighbor j ≠ s • F.val := by
  apply F.val.neighbor_ne_reflect_of_free j s.val
  intro k hk
  have hz : s • (flagVertex H D F k) = flagVertex H D F k := by
    apply Subtype.ext
    exact funext hk
  have hp : s • gridPoint h (F.val.vertex k) = gridPoint h (F.val.vertex k) := by
    calc
      _ = gridPoint h (s • F.val.vertex k) := (gridPoint_smul h s.val _).symm
      _ = _ := congrArg (gridPoint h) (congrArg Subtype.val hz)
  exact congrArg Subtype.val (hfree (flagVertex H D F k) s hp)

/-- The geometric complex now satisfies the abstract mod-two boundary lemma. -/
lemma another_boundary [Fintype D] (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (hc : n = Module.finrank ℝ V + 1)
    (haug : ∀ F : D, ∀ j : Fin (n + 1), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ F : D, ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k)))
    (h : ℝ) (hfree : ∀ z : vertices H D, ∀ s : H,
      s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (p₀ : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha))
    (hp₀ : p₀.val.cell.val.neighbor p₀.val.facet ∉ D) :
    ∃ p : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha),
      p.val.cell.val.neighbor p.val.facet ∉ D ∧
      ¬ (MulAction.orbitRel H _) p p₀ := by
  exact FinitePairing.exists_other_boundary D (cellHit H D a) (cellHit_equivariant H D ρ a ha)
    Flag.neighbor Flag.neighbor_neighbor (fun s F j ↦ (F.smul_neighbor s.val j).symm)
    (fun F j hh ↦ (cellHit_neighbor H D a F j).mpr hh)
    (fun F ↦ cellHit_even H D a F hc (haug F) (hvec F))
    (fun F j _ s ↦ neighbor_not_orbit H D h F hfree j s) p₀ hp₀

end PLComplex
end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.EquivariantFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u95 u96 u97 u98 u99 u100 u101 u102 u193 u194

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


namespace SharpLiebThirring.CubeFlags
open Finset

lemma embed_spatial_of_time_zero {d : ℕ} (x : Fin (d + 1) → ℝ) (hx : x (Fin.last d) = 0) :
    embedSpatial (spatial x) = x := by
  change Fin.snoc (Fin.init x) 0 = x
  rw [← hx, Fin.snoc_init_self]

lemma bottomSeed_time {d : ℕ} (h : ℝ) (p : Fin d → ℝ) (k : Fin (d + 2))
    (hk : k ≠ Fin.last (d + 1)) : (bottomSeed h p).point k (Fin.last d) = 0 := by
  rw [Flag.point_time_boundary _ _ (by simp [bottomSeed]) k hk]
  simp [bottomSeed]

lemma bottomSeed_dist_center {d : ℕ} (h : ℝ) (hh : 0 < h) (p : Fin d → ℝ) :
    dist (h • (bottomSeed h p).center) (embedSpatial p) ≤ h := by
  rw [dist_pi_le_iff hh.le]
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Pi.smul_apply, smul_eq_mul, Flag.center_apply, bottomSeed,
      Fin.snoc_last, Int.cast_zero, zero_add, embedSpatial, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h * (1/2))]
    linarith
  · have hl := Int.floor_le (p j / h)
    have hu := Int.lt_floor_add_one (p j / h)
    have hl' : h * (⌊p j / h⌋ : ℝ) ≤ p j := by
      have := (le_div_iff₀ hh).mp hl
      nlinarith
    have hu' : p j < h * ((⌊p j / h⌋ : ℝ) + 1) := by
      have := (div_lt_iff₀ hh).mp hu
      nlinarith
    simp only [Pi.smul_apply, smul_eq_mul, Flag.center_apply, bottomSeed,
      Fin.snoc_castSucc, embedSpatial, LinearMap.coe_mk, AddHom.coe_mk, Real.dist_eq, abs_le]
    constructor <;> nlinarith

lemma bottomSeed_dist_point {d : ℕ} (h : ℝ) (hh : 0 < h) (p : Fin d → ℝ)
    (k : Fin (d + 2)) : dist (h • (bottomSeed h p).point k) (embedSpatial p) ≤ 2 * h := by
  calc
    _ ≤ dist (h • (bottomSeed h p).point k) (h • (bottomSeed h p).center) +
      dist (h • (bottomSeed h p).center) (embedSpatial p) := dist_triangle _ _ _
    _ ≤ h / 2 + h := add_le_add ((bottomSeed h p).dist_scaled_point_center h hh.le k)
      (bottomSeed_dist_center h hh p)
    _ ≤ 2 * h := by linarith

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.InitialOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


/-! Disjoint equivariant coordinate balls for the unique initial zero orbit. -/

open Set Finset
namespace SharpLiebThirring.PLParity
section OrbitBalls
attribute [local instance] Classical.propDecidable
variable {G : Type u103} {E : Type u104} [Group G] [MetricSpace E] [MulAction G E]
  [IsIsometricSMul G E]

variable (p : E) (R : ℝ)

omit [IsIsometricSMul G E] in
lemma ballLabel_dist {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    dist x (ballLabel (G := G) p R x • p) < R := by
  rw [ballLabel, dif_pos hx]
  exact hx.choose_spec

variable (hR : 0 < R) (hsep : ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p))

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq {x : E} {g : G} (hx : dist x (g • p) < R) :
    ballLabel (G := G) p R x = g := by
  by_contra hn
  have hl := ballLabel_dist p R (show x ∈ orbitBall (G := G) p R from ⟨g,hx⟩)
  have hd := dist_triangle (ballLabel (G := G) p R x • p) x (g • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Signs.smul_time_zero {d : ℕ} (s : Signs (d + 1)) (x : Fin (d + 1) → ℝ)
    (hx : x (Fin.last d) = 0) : (s • x) (Fin.last d) = 0 := by
  simp only [Signs.smul_real, hx, neg_zero, ite_self]

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FreeLocus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129 u130 u131 u132 u133 u134 u135

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

section


/-! Analytic compactness and free-locus facts for the PL continuation proof. -/

open Set Finset

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Flag.dist_combination_gridPoint {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (F.combination h w) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, combination, dist_scale h hh]
  nlinarith [F.dist_combination_point w hw hs k]

lemma cellHit_weights {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u124} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (F : D) (j : Fin (n + 1)) (hj : cellHit H D a F.val j) :
    ∃ w : Fin (n + 1) → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧ w j = 0 ∧
      ∑ k, w k • a (flagVertex H D F k) = 0 := by
  obtain ⟨w,he,hj,hw⟩ := hj
  refine ⟨w,hw,?_,hj,?_⟩
  · exact congrArg Prod.fst he
  · simpa only [augmentedMap_apply, extendValues_at] using congrArg Prod.snd he

lemma Flag.combination_time_boundary {n : ℕ} [NeZero n] (F : Flag n) (h : ℝ)
    (t : Fin n) (ht : (F.order.symm t).val = n - 1)
    (w : Fin (n + 1) → ℝ) (hs : ∑ k, w k = 1) (hz : w (Fin.last n) = 0) :
    F.combination h w t = h * ((F.base t : ℝ) + if F.corner t then 1 else 0) := by
  change h * (∑ k, w k • F.point k) t = _
  rw [Finset.sum_apply]
  have he : (∑ k, w k * F.point k t) =
      ∑ k, w k * ((F.base t : ℝ) + if F.corner t then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = Fin.last n
    · simp only [hk,hz,zero_mul]
    · rw [F.point_time_boundary t ht k hk]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [he, ← Finset.sum_mul, hs, one_mul]

end SharpLiebThirring.CubeFlags
end

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Flag.combination_eq_sum_gridPoint {n : ℕ} (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) :
    F.combination h w = ∑ k, w k • gridPoint h (F.vertex k) := by
  simp only [combination, gridPoint_vertex, Finset.smul_sum, smul_comm h]

lemma Signs.smul_sum_real {n : ℕ} {ι : Type u126} [Fintype ι] (s : Signs n)
    (w : ι → ℝ) (x : ι → Fin n → ℝ) :
    s • (∑ i, w i • x i) = ∑ i, w i • (s • x i) := by
  change s.linearIsometry (∑ i, w i • x i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ map_smul s.linearIsometry (w i) (x i))

lemma Flag.combination_smul {n : ℕ} (s : Signs n) (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) : (s • F).combination h w = s • F.combination h w := by
  rw [Flag.combination_eq_sum_gridPoint, Flag.combination_eq_sum_gridPoint, s.smul_sum_real]
  apply Finset.sum_congr rfl
  intro k _
  rw [F.vertex_smul, gridPoint_smul]

lemma sum_affine_linear {ι : Type u127} {E : Type u128} {V : Type u129} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (L : E →ₗ[ℝ] V) (w : ι → ℝ) (hs : ∑ i, w i = 1) (x : ι → E) (q : E) :
    (∑ i, w i • L (x i - q)) = L ((∑ i, w i • x i) - q) := by
  simp only [map_sub, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hs, one_smul]

lemma cellHit_of_weights {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u130} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (F : D) (j : Fin (n + 1))
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w j = 0) (hz : ∑ k, w k • a (flagVertex H D F k) = 0) : cellHit H D a F.val j := by
  refine ⟨w,?_,hj,hw⟩
  apply Prod.ext
  · exact hs
  · simpa only [augmentedMap_apply, extendValues_at] using hz

lemma affine_sum_on_facet {ι : Type u131} {E : Type u132} {V : Type u133} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    (L : E →ₗ[ℝ] V) (w : ι → ℝ) (hs : ∑ i, w i = 1)
    (j : ι) (hj : w j = 0) (x : ι → E) (q : E) (a : ι → V)
    (ha : ∀ k, k ≠ j → a k = L (x k - q)) :
    ∑ k, w k • a k = L ((∑ k, w k • x k) - q) := by
  rw [← sum_affine_linear L w hs x q]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · simp only [hk, hj, zero_smul]
  · rw [ha k hk]

lemma mesh_affine_zero_point {d : ℕ} (H : Subgroup (Signs (d + 1)))
    {V : Type u134} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (F : Flag (d + 1)) (j : Fin (d + 2)) (h : ℝ) (s : H) (q : Fin d → ℝ)
    (w : Fin (d + 2) → ℝ) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (a : Fin (d + 2) → V) (hz : ∑ k, w k • a k = 0)
    (ha : ∀ k, k ≠ j → a k = ρ s (L (spatial (s⁻¹ • gridPoint h (F.vertex k)) - q)))
    (ht : F.combination h w (Fin.last d) = 0) :
    F.combination h w = s • embedSpatial q := by
  have he := affine_sum_on_facet (L.trans (ρ s)).toLinearMap w hs j hj
    (fun k ↦ spatial (s⁻¹ • gridPoint h (F.vertex k))) q a ha
  rw [hz] at he
  have hq : (∑ k, w k • spatial (s⁻¹ • gridPoint h (F.vertex k))) = q := by
    apply sub_eq_zero.mp
    apply (L.trans (ρ s)).injective
    change (L.trans (ρ s)) _ = (L.trans (ρ s)) 0
    rw [map_zero]
    exact he.symm
  have hsum : spatial (s⁻¹ • F.combination h w) = q := by
    rw [F.combination_eq_sum_gridPoint]
    rw [Subgroup.smul_def, Signs.smul_sum_real, map_sum]
    simpa only [map_smul, Subgroup.smul_def] using hq
  have ht' : (s⁻¹ • F.combination h w) (Fin.last d) = 0 :=
    s⁻¹.val.smul_time_zero _ ht
  have hx : s⁻¹ • F.combination h w = embedSpatial q := by
    rw [← hsum]
    exact (embed_spatial_of_time_zero _ ht').symm
  simpa only [smul_inv_smul] using congrArg (fun x ↦ s • x) hx

lemma model_seed_hit {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (D : SubMulAction H (Flag (d + 1)))
    {V : Type u135} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : 2*h < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (F : D) (hF : F.val = bottomSeed h p) (a : vertices H D → V)
    (ha : ∀ k, k ≠ Fin.last (d + 1) →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w (Fin.last (d + 1)) = 0)
    (he : ∑ k, w k • gridPoint h (F.val.vertex k) = embedSpatial q) :
    cellHit H D a F.val (Fin.last (d + 1)) := by
  apply cellHit_of_weights H D a F _ w hw hs hj
  have hv (k : Fin (d + 2)) : ballLabel (G := H) (embedSpatial p) R (gridPoint h (F.val.vertex k)) = 1 := by
    apply ballLabel_eq (embedSpatial p) R hR hsep
    rw [one_smul, hF, gridPoint_vertex]
    exact (bottomSeed_dist_point h hh p k).trans_lt hhr
  have haf (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      a (flagVertex H D F k) = L (spatial (gridPoint h (F.val.vertex k)) - q) := by
    rw [ha k hk]
    simp only [affineOrbitModel, hv, inv_one, one_smul, map_one]
    rfl
  rw [affine_sum_on_facet L.toLinearMap w hs _ hj
    (fun k ↦ spatial (gridPoint h (F.val.vertex k))) q _ haf]
  have hsp := congrArg spatial he
  simp only [map_sum, map_smul, spatial_embed] at hsp
  rw [hsp, sub_self, map_zero]

lemma bottom_facet_unique {d : ℕ} (h : ℝ) (hh : h ≠ 0) (p q : Fin d → ℝ)
    (s : Signs (d + 1)) (hst : s.val (Fin.last d) = false)
    (G : Flag (d + 1)) (hGb : G.base (Fin.last d) = 0) (hGc : G.corner (Fin.last d) = false)
    (w z : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w k) (hz : ∀ k, 0 ≤ z k)
    (hsw : ∑ k, w k = 1) (hsz : ∑ k, z k = 1)
    (he : (bottomSeed h p).combination h w = embedSpatial q)
    (hg : G.combination h z = s • embedSpatial q) : G = s • bottomSeed h p := by
  have hx : (s • bottomSeed h p).combination h w = G.combination h z := by
    rw [Flag.combination_smul, he, hg]
  have hx' := (smul_right_injective (Fin (d + 1) → ℝ) hh) hx
  apply Eq.symm
  apply Flag.eq_of_facet_combination _ _ (Fin.last d) _ _ _ w z hw hwp hz hsw hsz hx'
  · simp [Flag.smul_def, Flag.reflect, bottomSeed]
  · simp [Flag.smul_def, Flag.reflect, bottomSeed, hst, hGb]
  · simp [Flag.smul_def, Flag.reflect, bottomSeed, hst, hGc]

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundaryParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u136 u137 u138 u139 u140 u141 u142

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma bottom_hit_unique {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (D : SubMulAction H (Flag (d + 1)))
    {V : Type u136} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R / 2)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (a : vertices H D → V)
    (haf : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) (Fin.last d) = 0 →
      gridPoint h (F.val.vertex k) ∈ orbitBall (G := H) (embedSpatial p) R →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (w₀ : Fin (d + 2) → ℝ) (hw₀ : ∀ k, 0 ≤ w₀ k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w₀ k) (hs₀ : ∑ k, w₀ k = 1)
    (he₀ : (bottomSeed h p).combination h w₀ = embedSpatial q)
    (F : D) (ht : (F.val.order.symm (Fin.last d)).val = d)
    (hb : F.val.base (Fin.last d) = 0) (hc : F.val.corner (Fin.last d) = false)
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hj : w (Fin.last (d + 1)) = 0) (hz : ∑ k, w k • a (flagVertex H D F k) = 0)
    (hx : F.val.combination h w ∈ orbitBall (G := H) (embedSpatial p) (R / 2)) :
    ∃ s : H, F.val = s • bottomSeed h p := by
  obtain ⟨s,hxs⟩ := hx
  have hdist (k : Fin (d + 2)) : dist (gridPoint h (F.val.vertex k)) (s • embedSpatial p) < R := by
    calc
      _ ≤ dist (gridPoint h (F.val.vertex k)) (F.val.combination h w) +
          dist (F.val.combination h w) (s • embedSpatial p) := dist_triangle _ _ _
      _ < h + R / 2 := add_lt_add_of_le_of_lt
        (by rw [dist_comm]; exact F.val.dist_combination_gridPoint h hh.le w hw hs k) hxs
      _ ≤ R := by linarith
  have htime (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      gridPoint h (F.val.vertex k) (Fin.last d) = 0 := by
    rw [gridPoint_vertex]
    change h * F.val.point k (Fin.last d) = 0
    rw [F.val.point_time_boundary (Fin.last d) (by simpa using ht) k hk, hb, hc]
    simp
  have hlabel (k : Fin (d + 2)) :
      ballLabel (G := H) (embedSpatial p) R (gridPoint h (F.val.vertex k)) = s :=
    ballLabel_eq (embedSpatial p) R hR hsep (hdist k)
  have hval (k : Fin (d + 2)) (hk : k ≠ Fin.last (d + 1)) :
      a (flagVertex H D F k) = ρ s (L (spatial (s⁻¹ • gridPoint h (F.val.vertex k)) - q)) := by
    rw [haf F k (htime k hk) ⟨s,hdist k⟩]
    simp only [affineOrbitModel, hlabel]
  have hxt : F.val.combination h w (Fin.last d) = 0 := by
    rw [F.val.combination_time_boundary h (Fin.last d) (by simpa using ht) w hs hj, hb, hc]
    simp
  have hxq := mesh_affine_zero_point H ρ L F.val _ h s q w hs hj
    (fun k ↦ a (flagVertex H D F k)) hz hval hxt
  exact ⟨s, bottom_facet_unique h hh.ne' p q s.val (hHt s) F.val hb hc
    w₀ w hw₀ hwp hw hs₀ hs he₀ hxq⟩

/-- Finite equivariant parity rules out a bounded approximating cylinder whose
only boundary hits lie in the one initial root orbit. -/
lemma mesh_parity_contradiction_oai {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (D : SubMulAction H (Flag (d + 1))) [Fintype D]
    {V : Type u137} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p q : Fin d → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : 2*h < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (a : vertices H D → V) (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z))
    (haug : ∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
      (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k))))
    (hvec : ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
      (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k)))
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1)
    (haf : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) (Fin.last d) = 0 →
      gridPoint h (F.val.vertex k) ∈ orbitBall (G := H) (embedSpatial p) R →
      a (flagVertex H D F k) = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (F.val.vertex k)))
    (F₀ : D) (hF₀ : F₀.val = bottomSeed h p)
    (hout₀ : F₀.val.neighbor (Fin.last (d + 1)) ∉ D)
    (w₀ : Fin (d + 2) → ℝ) (hw₀ : ∀ k, 0 ≤ w₀ k)
    (hwp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w₀ k) (hs₀ : ∑ k, w₀ k = 1)
    (hj₀ : w₀ (Fin.last (d + 1)) = 0)
    (he₀ : (bottomSeed h p).combination h w₀ = embedSpatial q)
    (hbdy : ∀ F : D, ∀ j : Fin (d + 2), F.val.neighbor j ∉ D →
      ∀ w : Fin (d + 2) → ℝ, (∀ k, 0 ≤ w k) → ∑ k, w k = 1 → w j = 0 →
      ∑ k, w k • a (flagVertex H D F k) = 0 →
      j = Fin.last (d + 1) ∧ (F.val.order.symm (Fin.last d)).val = d ∧
      F.val.base (Fin.last d) = 0 ∧ F.val.corner (Fin.last d) = false ∧
      F.val.combination h w ∈ orbitBall (G := H) (embedSpatial p) (R / 2)) : False := by
  have hseed : cellHit H D a F₀.val (Fin.last (d + 1)) := by
    apply model_seed_hit H D ρ L p q R h hR hh hhr hsep F₀ hF₀ a
      (fun k hk ↦ haf F₀ k ?_ ?_) w₀ hw₀ hs₀ hj₀
    · rw [hF₀, ← Flag.combination_eq_sum_gridPoint]
      exact he₀
    · rw [hF₀, gridPoint_vertex]
      change h * (bottomSeed h p).point k (Fin.last d) = 0
      rw [bottomSeed_time h p k hk, mul_zero]
    · refine ⟨1,?_⟩
      rw [one_smul, hF₀, gridPoint_vertex]
      exact (bottomSeed_dist_point h hh p k).trans_lt hhr
  let p₀ : FinitePairing.selected D (cellHit H D a) (cellHit_equivariant H D ρ a ha) :=
    ⟨⟨F₀, Fin.last (d + 1)⟩, hseed⟩
  have hdim : d + 1 = Module.finrank ℝ V + 1 := by
    have he := L.finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using congrArg (· + 1) he
  obtain ⟨b,hb,hborb⟩ := another_boundary H D ρ a ha hdim haug hvec h hfree p₀ hout₀
  obtain ⟨w,hw,hs,hj,hz⟩ := cellHit_weights H D a b.val.cell b.val.facet b.prop
  obtain ⟨hjl,ht,hbase,hcorner,hx⟩ := hbdy b.val.cell b.val.facet hb w hw hs hj hz
  have hj' : w (Fin.last (d + 1)) = 0 := hjl ▸ hj
  obtain ⟨s,hF⟩ := bottom_hit_unique H hHt D ρ L p q R h hR hh (by linarith) hsep
    a haf w₀ hw₀ hwp hs₀ he₀ b.val.cell ht hbase hcorner w hw hs hj' hz hx
  apply hborb
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨s,?_⟩
  apply Subtype.ext
  apply FinitePairing.CellFacet.ext
  · apply Subtype.ext
    change s • F₀.val = b.val.cell.val
    rw [hF₀, hF]
  · exact hjl.symm

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

theorem solution.{u137} : type_of% @OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction_oai.{u137} := @OAI.SharpLiebThirring.CubeFlags.mesh_parity_contradiction_oai.{u137}
