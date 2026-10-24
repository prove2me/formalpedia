-- Prove2me | solution 1 for OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T14:02:00.761446+00:00
-- url     : https://prove2.me/submissions/94b91c19-23b9-48a4-ad1e-30b413339f1a

import Mathlib
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_CubeFlags_mesh_parity_contradiction

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

section Consecutive
variable {V : Type u37} [AddCommGroup V] [Module ℝ V]

lemma span_consecutive {n : ℕ} (v : Fin (n + 1) → V) :
    Submodule.span ℝ (Set.range (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc))) =
    Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨j.succ, rfl⟩)
        (Submodule.subset_span ⟨j.castSucc, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.induction ?_ (fun j hj ↦ ?_) i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · have hd : v j.succ - v j.castSucc ∈
          Submodule.span ℝ (Set.range (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc))) :=
        Submodule.subset_span ⟨j.succ, rfl⟩
      have hsum := Submodule.add_mem _ hd hj
      rw [sub_add_cancel] at hsum
      exact hsum

lemma linearIndependent_consecutive_iff {n : ℕ} (v : Fin (n + 1) → V) :
    LinearIndependent ℝ (Fin.cons (v 0) (fun i ↦ v i.succ - v i.castSucc)) ↔
    LinearIndependent ℝ v := by
  rw [linearIndependent_iff_card_eq_finrank_span, linearIndependent_iff_card_eq_finrank_span]
  change _ = Module.finrank ℝ (Submodule.span ℝ _) ↔ _ = Module.finrank ℝ (Submodule.span ℝ _)
  rw [span_consecutive]
end Consecutive

lemma Flag.step_ne_zero {n : ℕ} (F : Flag n) (i : Fin n) : F.step i ≠ 0 := by
  dsimp [step]
  split_ifs <;> norm_num

lemma Flag.point_succ_sub {n : ℕ} (F : Flag n) (k : Fin n) :
    F.point k.succ - F.point k.castSucc = Pi.single (F.order k) (F.step k) := by
  ext i
  by_cases hi : i = F.order k
  · subst i
    simp only [Pi.sub_apply, point, vertex, Equiv.symm_apply_apply,
      Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_self, ↓reduceIte, lt_self_iff_false,
      Pi.single_eq_same, step]
    split_ifs <;> push_cast <;> ring
  · have hik : F.order.symm i ≠ k := by
      intro h
      apply hi
      simpa using congrArg F.order h
    have hval : (F.order.symm i).val ≠ k.val := fun h ↦ hik (Fin.ext h)
    have hlt : (F.order.symm i).val < k.val + 1 ↔ (F.order.symm i).val < k.val := by omega
    simp [hi, point, vertex, hlt]

lemma Flag.linearIndependent_steps {n : ℕ} (F : Flag n) :
    LinearIndependent ℝ (fun k : Fin n ↦ F.point k.succ - F.point k.castSucc) := by
  classical
  have hb := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp F.order F.order.injective
  have hs := hb.units_smul (fun k ↦ Units.mk0 (F.step k) (F.step_ne_zero k))
  have he : (fun k : Fin n ↦ F.point k.succ - F.point k.castSucc) =
      (fun k ↦ Units.mk0 (F.step k) (F.step_ne_zero k)) •
        ((Pi.basisFun ℝ (Fin n)) ∘ F.order) := by
    funext k
    rw [F.point_succ_sub k]
    ext i
    simp [Pi.basisFun_apply, Pi.single_apply, Units.smul_def]
  rw [he]
  exact hs

lemma Flag.augmented_linearIndependent {n : ℕ} (F : Flag n) :
    LinearIndependent ℝ (fun k ↦ ((1 : ℝ), F.point k)) := by
  apply (linearIndependent_consecutive_iff _).mp
  apply linearIndependent_finCons.mpr
  constructor
  · have h := F.linearIndependent_steps.map' (LinearMap.inr ℝ ℝ (Fin n → ℝ))
      (LinearMap.ker_eq_bot.mpr LinearMap.inr_injective)
    simpa only [LinearMap.inr_apply, Function.comp_def, Prod.mk_sub_mk, sub_self] using h
  · have hspan : Submodule.span ℝ
        (Set.range (fun i : Fin n ↦ ((1 : ℝ), F.point i.succ) - (1, F.point i.castSucc))) ≤
        LinearMap.ker (LinearMap.fst ℝ ℝ (Fin n → ℝ)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp
    intro hmem
    have h := hspan hmem
    simp at h

lemma Flag.reflect_point {n : ℕ} (s : Fin n → Bool) (F : Flag n)
    (k : Fin (n + 1)) (i : Fin n) :
    (F.reflect s).point k i = if s i then -F.point k i else F.point k i := by
  dsimp [point]
  rw [reflect_vertex]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;> simp [hs]
  ring

lemma Flag.smul_def {n : ℕ} (s : Signs n) (F : Flag n) : s • F = F.reflect s.val := rfl

/-- No two vertices of a flag belong to the same coordinate-reflection orbit.
Parity records the order in which coordinates become barycenters. -/
lemma Flag.vertex_orbits_distinct {n : ℕ} (F : Flag n)
    (j k : Fin (n + 1)) (s : Signs n)
    (he : ∀ i, F.vertex j i = if s.val i then -F.vertex k i else F.vertex k i) : j = k := by
  apply Fin.ext
  by_contra h
  have hlt : j.val < k.val ∨ k.val < j.val := lt_or_gt_of_ne h
  have hbad (a b : Fin (n + 1)) (hab : a.val < b.val)
      (hh : ∀ i, F.vertex a i = if s.val i then -F.vertex b i else F.vertex b i) : False := by
    let i : Fin n := F.order ⟨a.val, by omega⟩
    have hi : (F.order.symm i).val = a.val := by simp [i]
    have hh' := hh i
    simp only [vertex, hi, lt_self_iff_false, ↓reduceIte, hab] at hh'
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
      simp [hs, hc] at hh' <;> omega
  rcases hlt with hlt | hlt
  · exact hbad j k hlt he
  · apply hbad k j hlt
    intro i
    have hi := he i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      simp_all

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

lemma Flag.combination_bounds {n : ℕ} (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (i : Fin n) :
    (F.base i : ℝ) ≤ (∑ k, w k • F.point k) i ∧
      (∑ k, w k • F.point k) i ≤ F.base i + 1 := by
  have h₀ := F.depth_nonneg w hw hs i
  have h₁ := F.depth_le_half w hw hs i
  rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp only [depth, hc, Bool.false_eq_true, ↓reduceIte] at h₀ h₁ <;>
    constructor <;> linarith

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

lemma Flag.point_smul {n : ℕ} (s : Signs n) (F : Flag n) (k : Fin (n + 1)) :
    (s • F).point k = s • F.point k := by
  ext i
  exact F.reflect_point s.val k i

lemma Flag.center_smul {n : ℕ} (s : Signs n) (F : Flag n) :
    (s • F).center = s • F.center := F.point_smul s _

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

lemma Flag.finite_base_bounds {n : ℕ} (L U : ℤ) :
    Set.Finite {F : Flag n | ∀ i, L ≤ F.base i ∧ F.base i ≤ U} := by
  let e : {F : Flag n // ∀ i, L ≤ F.base i ∧ F.base i ≤ U} →
      ((Fin n → ↥(Finset.Icc L U)) × (Fin n → Bool) × Equiv.Perm (Fin n)) :=
    fun F ↦ (fun i ↦ ⟨F.val.base i, by simpa only [Finset.mem_Icc] using F.prop i⟩,
      F.val.corner, F.val.order)
  have he : Function.Injective e := by
    intro F G h
    apply Subtype.ext
    apply Flag.ext
    · funext i
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
    · exact congrArg (fun z ↦ z.2.1) h
    · exact congrArg (fun z ↦ z.2.2) h
  exact Set.finite_def.mpr ⟨Fintype.ofInjective e he⟩

/-- Cubes whose centers are close to a compact set form a finite collection. -/
lemma Flag.finite_near_centers {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K)
    (h r : ℝ) (hh : 0 < h) :
    Set.Finite {F : Flag n | ∃ x ∈ K, dist (h • F.center) x < r} := by
  obtain ⟨B, hB⟩ := hK.exists_norm_le
  obtain ⟨U, hU⟩ := exists_int_gt ((B + r) / h + 1)
  apply (Flag.finite_base_bounds (-U) U).subset
  rintro F ⟨x, hx, hd⟩ i
  have hc : ‖h • F.center‖ < B + r := by
    have ht := norm_add_le (h • F.center - x) x
    rw [sub_add_cancel, ← dist_eq_norm] at ht
    linarith [hB x hx]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh] at hc
  have hc' : ‖F.center‖ < (B + r) / h := (lt_div_iff₀ hh).mpr (by nlinarith)
  have hi : |F.center i| ≤ ‖F.center‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm F.center i
  rw [F.center_apply] at hi
  have hl : -(U : ℝ) ≤ F.base i := by
    have := (abs_le.mp hi).1
    linarith
  have hu : (F.base i : ℝ) ≤ U := by
    have := (abs_le.mp hi).2
    linarith
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

lemma finite_nearCylinder {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K)
    (h r : ℝ) (hh : 0 < h) (t : Fin n) (m : ℕ) : (nearCylinder K h r t m).Finite :=
  (Flag.finite_near_centers hK h r hh).subset (fun _ hF ↦ hF.1)

lemma nearCylinder_smul {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ) (t : Fin n) (m : ℕ)
    (s : Signs n) (ht : s.val t = false) (hK : ∀ x ∈ K, s • x ∈ K)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m) : s • F ∈ nearCylinder K h r t m := by
  obtain ⟨⟨x, hx, hd⟩, hlo, hhi⟩ := hF
  refine ⟨⟨s • x, hK x hx, ?_⟩, ?_, ?_⟩
  · rw [F.center_smul]
    have he : h • (s • F.center) = s • (h • F.center) := by
      ext i
      simp only [Pi.smul_apply, Signs.smul_real, smul_eq_mul]
      rcases Bool.eq_false_or_eq_true (s.val i) with hi | hi <;> simp [hi]
      ring
    rw [he, dist_smul]
    exact hd
  · simpa only [Flag.smul_def, Flag.reflect, ht, Bool.false_eq_true, ↓reduceIte] using hlo
  · simpa only [Flag.smul_def, Flag.reflect, ht, Bool.false_eq_true, ↓reduceIte] using hhi

lemma nearCylinder_point_cthickening {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (k : Fin (n + 1)) : h • F.point k ∈ Metric.cthickening (r + h / 2) K := by
  obtain ⟨x, hx, hd⟩ := hF.1
  apply Metric.mem_cthickening_of_dist_le _ x _ K hx
  calc
    _ ≤ dist (h • F.point k) (h • F.center) + dist (h • F.center) x := dist_triangle _ _ _
    _ ≤ h / 2 + r := add_le_add (F.dist_scaled_point_center h hh k) hd.le
    _ = r + h / 2 := add_comm _ _


lemma Flag.neighbor_base_of_ne_last {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1))
    (hj : j ≠ Fin.last n) : (F.neighbor j).base = F.base := by
  have hn : j.val ≠ n := fun h ↦ hj (Fin.ext h)
  by_cases hz : j.val = 0
  · simp only [neighbor, dite_eq_left hz, flip_base]
  · simp only [neighbor, dite_eq_right hz, dite_eq_right hn, swap]

/-- A time-boundary facet is exactly the last facet of a flag expanding time last. -/
lemma Flag.neighbor_outside_time {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1))
    (t : Fin n) (m : ℤ) (hlo : 0 ≤ F.base t) (hhi : F.base t < m)
    (hout : ¬ (0 ≤ (F.neighbor j).base t ∧ (F.neighbor j).base t < m)) :
    j = Fin.last n ∧ (F.order.symm t).val = n - 1 ∧
      ((F.base t = 0 ∧ F.corner t = false) ∨ (F.base t = m - 1 ∧ F.corner t = true)) := by
  have hj : j = Fin.last n := by
    by_contra hj
    rw [F.neighbor_base_of_ne_last j hj] at hout
    exact hout ⟨hlo, hhi⟩
  have hp : 0 < n := NeZero.pos n
  have hc : F.neighbor j = F.cross (F.order ⟨n - 1, by omega⟩) := by
    subst j
    simp only [neighbor, Fin.val_last, ne_of_gt hp, ↓reduceDIte]
  rw [hc] at hout
  have ht : t = F.order ⟨n - 1, by omega⟩ := by
    by_contra ht
    simp only [cross, Function.update_of_ne ht] at hout
    exact hout ⟨hlo, hhi⟩
  refine ⟨hj, ?_, ?_⟩
  · rw [ht, Equiv.symm_apply_apply]
  · have hh : (F.cross (F.order ⟨n - 1, by omega⟩)).base t =
        F.base t + if F.corner t then 1 else -1 := by
      simp only [cross, ← ht, Function.update_self]
    simp only [hh] at hout
    rcases Bool.eq_false_or_eq_true (F.corner t) with htrue | hfalse
    · simp only [htrue, ↓reduceIte] at hout
      exact Or.inr ⟨by omega, htrue⟩
    · simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hout
      exact Or.inl ⟨by omega, hfalse⟩

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

lemma nearCylinder_point_time {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) (hm : h * m = 1)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m) (k : Fin (n + 1)) :
    (h • F.point k) t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := F.point_bounds k t
  have hb : (0 : ℝ) ≤ F.base t := by exact_mod_cast hF.2.1
  have hc : (F.base t : ℝ) + 1 ≤ m := by
    have hh := hF.2.2
    exact_mod_cast (show F.base t + 1 ≤ (m : ℤ) by omega)
  change 0 ≤ h * F.point k t ∧ h * F.point k t ≤ 1
  constructor
  · exact mul_nonneg hh (by linarith)
  · nlinarith

lemma nearCylinder_combination_time {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) (hm : h * m = 1)
    {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    (h • (∑ k, w k • F.point k)) t ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := F.combination_bounds w hw hs t
  have hb : (0 : ℝ) ≤ F.base t := by exact_mod_cast hF.2.1
  have hc : (F.base t : ℝ) + 1 ≤ m := by
    have hh := hF.2.2
    exact_mod_cast (show F.base t + 1 ≤ (m : ℤ) by omega)
  change 0 ≤ h * (∑ k, w k • F.point k) t ∧ h * (∑ k, w k • F.point k) t ≤ 1
  constructor
  · exact mul_nonneg hh (by linarith)
  · nlinarith

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

section VertexComplex
variable {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))

lemma flagVertex_orbits_injective (F : D) :
    Function.Injective (fun k ↦ (Quotient.mk'' (flagVertex H D F k) :
      Quotient (MulAction.orbitRel H (vertices H D)))) := by
  intro j k he
  have hr := Quotient.exact' he
  obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
  have hh : F.val.vertex j = s.val • F.val.vertex k := (congrArg Subtype.val hs).symm
  apply F.val.vertex_orbits_distinct j k s.val
  intro i
  exact congrFun hh i

/-- Freeness of the real vertex positions induces freeness on the finite
vertex set. It is supplied by the compact free-locus tube, not presumed. -/
theorem verticesIsCancel (h : ℝ)
    (hfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1) :
    IsCancelSMul H (vertices H D) where
  right_cancel' s t z he := by
    have he' : s • z.val = t • z.val := congrArg Subtype.val he
    have he'' : (t⁻¹ * s) • z.val = z.val := by
      rw [mul_smul, he', inv_smul_smul]
    have hp : (t⁻¹ * s) • gridPoint h z.val = gridPoint h z.val := by
      calc
        _ = gridPoint h ((t⁻¹ * s) • z.val) := (gridPoint_smul h (t⁻¹ * s).val z.val).symm
        _ = _ := congrArg (gridPoint h) he''
    exact (inv_mul_eq_one.mp (hfree z _ hp)).symm

end VertexComplex
end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.GenericPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u68 u69 u70 u71 u72 u73 u74 u75 u76 u77 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u191 u192

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


section


/-! Generic vertex positions for the piecewise-linear continuation argument. -/

open Set Finset Filter
namespace SharpLiebThirring.PLParity

variable {V : Type u68} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
lemma dense_compl_proper_submodule (S : Submodule ℝ V) (hS : S ≠ ⊤) :
    Dense (S : Set V)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra h
  exact hS (S.eq_top_of_nonempty_interior' (Set.nonempty_iff_ne_empty.mpr h))

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent_extension {ι : Type u71} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ v) (n : ℕ)
    (hn : Fintype.card ι + n ≤ Module.finrank ℝ V) :
    Dense {w : Fin n → V | LinearIndependent ℝ (Sum.elim v w)} := by
  classical
  induction n with
  | zero =>
      have he : {w : Fin 0 → V | LinearIndependent ℝ (Sum.elim v w)} = Set.univ := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rw [linearIndependent_sum]
        refine ⟨hv, linearIndependent_empty_type, ?_⟩
        simp
      rw [he]
      exact dense_univ
  | succ n ih =>
      rw [Metric.dense_iff]
      intro w ε hε
      obtain ⟨z, hz, hzε⟩ := (ih (by omega)).exists_dist_lt (Fin.tail w) hε
      let S : Submodule ℝ V := Submodule.span ℝ (Set.range (Sum.elim v z))
      have hS : S ≠ ⊤ := by
        intro he
        have hd := finrank_span_eq_card hz
        change Module.finrank ℝ S = Fintype.card (ι ⊕ Fin n) at hd
        rw [he, finrank_top, Fintype.card_sum, Fintype.card_fin] at hd
        omega
      obtain ⟨x, hx, hxε⟩ := (dense_compl_proper_submodule S hS).exists_dist_lt (w 0) hε
      refine ⟨Fin.cons x z, ?_, ?_⟩
      · apply (dist_pi_lt_iff hε).mpr
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa [dist_comm] using hxε
        · simpa [Fin.tail, dist_comm] using (dist_pi_lt_iff hε).mp hzε j
      · have hl := (hz.option hx).comp (sumFinSuccEmbedding ι n)
          (sumFinSuccEmbedding ι n).injective
        change LinearIndependent ℝ (Sum.elim v (Fin.cons x z))
        have heq : Sum.elim v (Fin.cons x z) =
            (fun o ↦ o.casesOn' x (Sum.elim v z)) ∘ (sumFinSuccEmbedding ι n) := by
          ext i
          rcases i with i | i
          · rfl
          · exact Fin.cases rfl (fun j ↦ rfl) i
        rw [heq]
        exact hl

lemma dense_augmentedIndependent_extension_fin {ι : Type u73} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) (n : ℕ)
    (hn : Fintype.card ι + n ≤ Module.finrank ℝ V + 1) :
    Dense {w : Fin n → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), Sum.elim v w i))} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let a : Fin n → ℝ × V := fun i ↦ (1, w i)
  let normal : (Fin n → ℝ × V) → (Fin n → V) := fun u i ↦ (u i).1⁻¹ • (u i).2
  have hnorm : ContinuousAt normal a := by
    apply continuousAt_pi.mpr
    intro i
    exact (((continuous_apply i).fst.continuousAt).inv₀ (by norm_num [a])).smul
      (continuous_apply i).snd.continuousAt
  have hnval : normal a = w := by ext i; simp [normal, a]
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousAt_iff.mp hnorm ε hε
  obtain ⟨u, hu, huδ⟩ := (dense_linearIndependent_extension
    (V := ℝ × V) (fun i ↦ ((1 : ℝ), v i)) hv n
    (by simpa [Module.finrank_prod, Nat.add_comm] using hn)).exists_dist_lt a
    (lt_min hδ (by norm_num : (0 : ℝ) < 1))
  rw [dist_comm] at huδ
  have hfst (i : Fin n) : (u i).1 ≠ 0 := by
    intro he
    have hdi : dist (u i) (a i) < 1 :=
      lt_of_lt_of_le ((dist_pi_lt_iff (lt_min hδ (by norm_num))).mp huδ i) (min_le_right _ _)
    rw [Prod.dist_eq] at hdi
    have hdf := (max_lt_iff.mp hdi).1
    simp [he, a] at hdf
  refine ⟨normal u, ?_, ?_⟩
  · have hd := hcδ (lt_of_lt_of_le huδ (min_le_left _ _))
    simpa [hnval, dist_comm] using hd
  · let c : ι ⊕ Fin n → ℝˣ := Sum.elim (fun _ ↦ 1)
      (fun i ↦ (Units.mk0 (u i).1 (hfst i))⁻¹)
    have hul := hu.units_smul c
    change LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v (normal u) i))
    have heq : (fun i ↦ ((1 : ℝ), Sum.elim v (normal u) i)) =
        c • Sum.elim (fun i ↦ ((1 : ℝ), v i)) u := by
      funext i
      rcases i with i | i <;> ext <;> simp [c, normal, Units.smul_def, hfst]
    rw [heq]
    exact hul

omit [FiniteDimensional ℝ V] in
lemma dense_linearIndependent_extension_fintype {ι : Type u74} {κ : Type u75} [Fintype ι] [Fintype κ]
    (v : ι → V) (hv : LinearIndependent ℝ v)
    (hn : Fintype.card ι + Fintype.card κ ≤ Module.finrank ℝ V) :
    Dense {w : κ → V | LinearIndependent ℝ (Sum.elim v w)} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let e := Fintype.equivFin κ
  obtain ⟨z, hz, hzε⟩ := (dense_linearIndependent_extension v hv (Fintype.card κ) hn).exists_dist_lt (w ∘ e.symm) hε
  refine ⟨z ∘ e, ?_, ?_⟩
  · apply (dist_pi_lt_iff hε).mpr
    intro i
    simpa [Function.comp_def, dist_comm] using (dist_pi_lt_iff hε).mp hzε (e i)
  · have heq : Sum.elim v (z ∘ e) =
        (Sum.elim v z) ∘ (Equiv.sumCongr (Equiv.refl ι) e) := by
      funext i
      cases i <;> rfl
    change LinearIndependent ℝ (Sum.elim v (z ∘ e))
    rw [heq]
    exact hz.comp _ (Equiv.sumCongr (Equiv.refl ι) e).injective

lemma dense_augmentedIndependent_extension {ι : Type u76} {κ : Type u77} [Fintype ι] [Fintype κ]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι + Fintype.card κ ≤ Module.finrank ℝ V + 1) :
    Dense {w : κ → V | LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v w i))} := by
  classical
  rw [Metric.dense_iff]
  intro w ε hε
  let e := Fintype.equivFin κ
  obtain ⟨z, hz, hzε⟩ := (dense_augmentedIndependent_extension_fin v hv (Fintype.card κ) hn).exists_dist_lt (w ∘ e.symm) hε
  refine ⟨z ∘ e, ?_, ?_⟩
  · apply (dist_pi_lt_iff hε).mpr
    intro i
    simpa [Function.comp_def, dist_comm] using (dist_pi_lt_iff hε).mp hzε (e i)
  · have heq : (fun i ↦ ((1 : ℝ), Sum.elim v (z ∘ e) i)) =
        (fun i ↦ ((1 : ℝ), Sum.elim v z i)) ∘ (Equiv.sumCongr (Equiv.refl ι) e) := by
      funext i
      cases i <;> rfl
    change LinearIndependent ℝ (fun i ↦ ((1 : ℝ), Sum.elim v (z ∘ e) i))
    rw [heq]
    exact hz.comp _ (Equiv.sumCongr (Equiv.refl ι) e).injective

omit [FiniteDimensional ℝ V] in
lemma affineIndependent_of_augmented {ι : Type u78} (v : ι → V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) : AffineIndependent ℝ v := by
  rw [affineIndependent_iff]
  intro s w hs hsum i hi
  apply (linearIndependent_iff'.mp hv) s w _ i hi
  apply Prod.ext
  · simpa [Prod.fst_sum] using hs
  · simpa [Prod.snd_sum] using hsum

omit [FiniteDimensional ℝ V] in
lemma independent_shift_of_augmented_extra {ι : Type u79} (v : ι → V) (a : V)
    (hv : LinearIndependent ℝ
      (fun i : ι ⊕ Unit ↦ ((1 : ℝ), Sum.elim v (fun _ ↦ a) i))) :
    LinearIndependent ℝ (fun i ↦ v i - a) := by
  have hh := (affineIndependent_iff_linearIndependent_vsub ℝ
    (Sum.elim v (fun _ : Unit ↦ a)) (Sum.inr ())).mp (affineIndependent_of_augmented _ hv)
  let e : ι → {i : ι ⊕ Unit // i ≠ Sum.inr ()} := fun i ↦ ⟨Sum.inl i, by simp⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Sum.inl.inj (congrArg Subtype.val hij)
  exact hh.comp e he

/-- A generic root avoids the affine hull of every prescribed independent
proper face. This permits an initial zero inside exactly one maximal flag. -/
lemma dense_independent_shift {ι : Type u80} [Fintype ι] (v : ι → V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {a : V | LinearIndependent ℝ (fun i ↦ v i - a)} := by
  classical
  rw [Metric.dense_iff]
  intro a ε hε
  have hc : Fintype.card ι + Fintype.card Unit ≤ Module.finrank ℝ V + 1 := by
    simpa using Nat.add_le_add_right hn 1
  obtain ⟨w, hw, hwε⟩ := (dense_augmentedIndependent_extension v hv hc).exists_dist_lt
    (fun _ : Unit ↦ a) hε
  refine ⟨w (), ?_, independent_shift_of_augmented_extra v (w ()) ?_⟩
  · exact (dist_comm _ _).le.trans_lt ((dist_pi_lt_iff hε).mp hwε ())
  · have he : w = (fun _ : Unit ↦ w ()) := by funext i; cases i; rfl
    rw [he] at hw
    exact hw

omit [FiniteDimensional ℝ V] in
lemma isOpen_independent_shift {ι : Type u81} [Fintype ι] (v : ι → V) :
    IsOpen {a : V | LinearIndependent ℝ (fun i ↦ v i - a)} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  exact continuous_pi (fun _ ↦ continuous_const.sub continuous_id)

/-- Positive barycentric coordinates remain positive on a neighborhood when
an augmented vertex family is a basis. -/
lemma positive_barycentric_neighborhood {ι : Type u82} [Fintype ι]
    (v : ι → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (hn : Fintype.card ι = Module.finrank ℝ V + 1)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    ∃ U : Set V, IsOpen U ∧ (∑ i, w i • v i) ∈ U ∧
      ∀ x ∈ U, ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧ ∑ i, z i = 1 ∧ ∑ i, z i • v i = x := by
  classical
  let B : Module.Basis ι ℝ (ℝ × V) := basisOfLinearIndependentOfCardEqFinrank'
    (fun i ↦ ((1 : ℝ), v i)) hv (by simpa [Module.finrank_prod, Nat.add_comm] using hn)
  have hB (i : ι) : B i = ((1 : ℝ), v i) := by
    simp [B]
  let z : V → ι → ℝ := fun x ↦ B.equivFun (1, x)
  have hz : Continuous z := B.equivFun.toContinuousLinearEquiv.continuous.comp
    (continuous_const.prodMk continuous_id)
  have hrep (x : V) : ∑ i, z x i • ((1 : ℝ), v i) = (1, x) := by
    simpa only [z, Module.Basis.equivFun_apply, hB] using B.sum_repr (1, x)
  let x₀ : V := ∑ i, w i • v i
  have hzw : z x₀ = w := by
    apply B.equivFun.symm.injective
    change B.equivFun.symm (B.equivFun (1, x₀)) = B.equivFun.symm w
    rw [B.equivFun.symm_apply_apply, Module.Basis.equivFun_symm_apply]
    apply Prod.ext
    · simp only [hB, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, mul_one, hs]
    · simp only [hB, Prod.snd_sum, Prod.smul_snd]
      rfl
  refine ⟨{x | ∀ i, 0 < z x i}, ?_, ?_, ?_⟩
  · have ho : IsOpen (⋂ i, {x | (0 : ℝ) < z x i}) := isOpen_iInter_of_finite
      (fun i ↦ isOpen_lt continuous_const ((continuous_apply i).comp hz))
    simpa only [Set.ofPred_forall] using ho
  · change ∀ i, 0 < z x₀ i
    rwa [hzw]
  · intro x hx
    refine ⟨z x, hx, ?_, ?_⟩
    · simpa only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul, mul_one] using congrArg Prod.fst (hrep x)
    · simpa only [Prod.snd_sum, Prod.smul_snd] using congrArg Prod.snd (hrep x)

section VertexEvaluation
variable {Q : Type u83} {ι : Type u84} [Fintype Q] [Fintype ι]

omit [FiniteDimensional ℝ V] [Fintype Q] [Fintype ι] in
lemma vertexEvaluation_surjective (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) : Function.Surjective (vertexEvaluation e A) := by
  classical
  intro v
  refine ⟨Function.extend e (fun i ↦ (A i).symm (v i)) 0, ?_⟩
  ext i
  simp only [vertexEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
    he.extend_apply, LinearEquiv.apply_symm_apply]

lemma vertexEvaluation_isOpenMap (e : ι → Q) (he : Function.Injective e)
    (A : ι → V ≃ₗ[ℝ] V) : IsOpenMap (vertexEvaluation e A) :=
  (vertexEvaluation e A).toContinuousLinearMap.isOpenMap
    (vertexEvaluation_surjective e he A)

/-- Genericity may be imposed while retaining an independent prescribed part.
This is used for the initial boundary of the continuation cylinder. -/
lemma dense_vertex_independent_extension {κ : Type u85} [Fintype κ]
    (v : κ → V) (hv : LinearIndependent ℝ v)
    (e : ι → Q) (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hn : Fintype.card κ + Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {w : Q → V | LinearIndependent ℝ (Sum.elim v (vertexEvaluation e A w))} :=
  (dense_linearIndependent_extension_fintype v hv hn).preimage
    (vertexEvaluation_isOpenMap e he A)

lemma dense_vertex_augmented_extension {κ : Type u86} [Fintype κ]
    (v : κ → V) (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (e : ι → Q) (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hn : Fintype.card κ + Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {w : Q → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), Sum.elim v (vertexEvaluation e A w) i))} :=
  (dense_augmentedIndependent_extension v hv hn).preimage
    (vertexEvaluation_isOpenMap e he A)

attribute [local instance] Classical.propDecidable

omit [Fintype Q] [Fintype ι] in
lemma mixedVertexEvaluation_continuous (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) : Continuous (mixedVertexEvaluation P b e A) := by
  apply continuous_pi
  intro i
  by_cases h : P (e i)
  · simp only [mixedVertexEvaluation, dite_eq_left h]
    exact continuous_const
  · simp only [mixedVertexEvaluation, dite_eq_right h]
    exact (A i).toContinuousLinearEquiv.continuous.comp (continuous_apply (⟨e i, h⟩ : {q // ¬ P q}))

omit [Fintype Q] in
lemma isOpen_mixed_independent (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} :=
  isOpen_setOfPred_linearIndependent.preimage (mixedVertexEvaluation_continuous P b e A)

omit [Fintype Q] in
lemma isOpen_mixed_augmented (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) :
    IsOpen {a : {q // ¬ P q} → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} := by
  apply isOpen_setOfPred_linearIndependent.preimage
  exact continuous_pi (fun i ↦ continuous_const.prodMk
    ((continuous_apply i).comp (mixedVertexEvaluation_continuous P b e A)))

lemma dense_mixed_independent (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hfixed : LinearIndependent ℝ (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V) :
    Dense {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} := by
  let e' : {i // ¬ P (e i)} → {q // ¬ P q} := fun i ↦ ⟨e i.val, i.prop⟩
  have he' : Function.Injective e' := by
    intro i j h
    exact Subtype.ext (he (congrArg Subtype.val h))
  have hc : Fintype.card {i // P (e i)} + Fintype.card {i // ¬ P (e i)} = Fintype.card ι := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl (fun i ↦ P (e i)))
  have hh := dense_vertex_independent_extension
    (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))) hfixed
    e' he' (fun i ↦ A i.val) (by rw [hc]; exact hn)
  have heval (a : {q // ¬ P q} → V) :
      mixedVertexEvaluation P b e A a ∘ Equiv.sumCompl (fun i ↦ P (e i)) =
      Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a) := by
    funext i
    cases i with
    | inl i => simp [mixedVertexEvaluation, i.prop]
    | inr i => simp [mixedVertexEvaluation, vertexEvaluation, e', i.prop]
  have hset : {a : {q // ¬ P q} → V | LinearIndependent ℝ (mixedVertexEvaluation P b e A a)} =
      {a | LinearIndependent ℝ (Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a))} := by
    ext a
    exact (linearIndependent_equiv' (Equiv.sumCompl (fun i ↦ P (e i))) (heval a)).symm
  rwa [hset]

lemma dense_mixed_augmented (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (he : Function.Injective e) (A : ι → V ≃ₗ[ℝ] V)
    (hfixed : LinearIndependent ℝ
      (fun i : {i // P (e i)} ↦ ((1 : ℝ), A i.val (b (e i.val)))))
    (hn : Fintype.card ι ≤ Module.finrank ℝ V + 1) :
    Dense {a : {q // ¬ P q} → V | LinearIndependent ℝ
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} := by
  let e' : {i // ¬ P (e i)} → {q // ¬ P q} := fun i ↦ ⟨e i.val, i.prop⟩
  have he' : Function.Injective e' := by
    intro i j h
    exact Subtype.ext (he (congrArg Subtype.val h))
  have hc : Fintype.card {i // P (e i)} + Fintype.card {i // ¬ P (e i)} = Fintype.card ι := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl (fun i ↦ P (e i)))
  have hh := dense_vertex_augmented_extension
    (fun i : {i // P (e i)} ↦ A i.val (b (e i.val))) hfixed
    e' he' (fun i ↦ A i.val) (by rw [hc]; exact hn)
  have heval (a : {q // ¬ P q} → V) :
      (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i)) ∘ Equiv.sumCompl (fun i ↦ P (e i)) =
      (fun i ↦ ((1 : ℝ), Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
        (vertexEvaluation e' (fun i ↦ A i.val) a) i)) := by
    funext i
    cases i with
    | inl i => simp [mixedVertexEvaluation, i.prop]
    | inr i => simp [mixedVertexEvaluation, vertexEvaluation, e', i.prop]
  have hset : {a : {q // ¬ P q} → V | LinearIndependent ℝ
        (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a i))} =
      {a | LinearIndependent ℝ (fun i ↦ ((1 : ℝ),
        Sum.elim (fun i : {i // P (e i)} ↦ A i.val (b (e i.val)))
          (vertexEvaluation e' (fun i ↦ A i.val) a) i))} := by
    ext a
    exact (linearIndependent_equiv' (Equiv.sumCompl (fun i ↦ P (e i))) (heval a)).symm
  rwa [hset]

end VertexEvaluation

/-- Finitely many open genericity conditions can be imposed at once. -/
lemma dense_finite_conditions {X : Type u89} {κ : Type u90} [TopologicalSpace X] [Finite κ]
    (P : κ → X → Prop) (ho : ∀ k, IsOpen {x | P k x}) (hd : ∀ k, Dense {x | P k x}) :
    Dense {x | ∀ k, P k x} := by
  have h := (Set.finite_range (fun k ↦ {x | P k x})).dense_sInter
    (by rintro _ ⟨k, rfl⟩; exact ho k) (by rintro _ ⟨k, rfl⟩; exact hd k)
  simpa only [sInter_range, mem_iInter, mem_ofPred_eq, ofPred_forall] using h

/-- Arbitrarily small generic perturbations of finitely many equivariant vertex
values, with an already generic prescribed part retained exactly. The orbit
labels and transports are abstract here; a free finite group action supplies them. -/
lemma exists_mixed_generic
    {Q : Type u91} {W : Type u92} {T₁ : Type u93} {T₂ : Type u94} [Fintype Q] [Fintype W] [Fintype T₁] [Fintype T₂]
    (J₁ : T₁ → Type u191) (J₂ : T₂ → Type u192) [∀ t, Fintype (J₁ t)] [∀ t, Fintype (J₂ t)]
    (P : Q → Prop) (b : Q → V) (e : W → Q) (A : W → V ≃ₗ[ℝ] V)
    (v₁ : ∀ t, J₁ t → W) (v₂ : ∀ t, J₂ t → W)
    (he₁ : ∀ t, Function.Injective (e ∘ v₁ t))
    (he₂ : ∀ t, Function.Injective (e ∘ v₂ t))
    (hf₁ : ∀ t, LinearIndependent ℝ
      (fun i : {i // P (e (v₁ t i))} ↦ A (v₁ t i.val) (b (e (v₁ t i.val)))))
    (hf₂ : ∀ t, LinearIndependent ℝ
      (fun i : {i // P (e (v₂ t i))} ↦ ((1 : ℝ), A (v₂ t i.val) (b (e (v₂ t i.val))))))
    (hc₁ : ∀ t, Fintype.card (J₁ t) ≤ Module.finrank ℝ V)
    (hc₂ : ∀ t, Fintype.card (J₂ t) ≤ Module.finrank ℝ V + 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : {q // ¬ P q} → V,
      (∀ w, dist (mixedVertexEvaluation P b e A a w) (A w (b (e w))) < ε) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ mixedVertexEvaluation P b e A a (v₁ t i))) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a (v₂ t i)))) := by
  classical
  let C : T₁ ⊕ T₂ → ({q // ¬ P q} → V) → Prop := Sum.elim
    (fun t a ↦ LinearIndependent ℝ (fun i ↦ mixedVertexEvaluation P b e A a (v₁ t i)))
    (fun t a ↦ LinearIndependent ℝ (fun i ↦ ((1 : ℝ), mixedVertexEvaluation P b e A a (v₂ t i))))
  have hco : ∀ t, IsOpen {a | C t a} := by
    rintro (t | t)
    · exact isOpen_mixed_independent P b (e ∘ v₁ t) (fun i ↦ A (v₁ t i))
    · exact isOpen_mixed_augmented P b (e ∘ v₂ t) (fun i ↦ A (v₂ t i))
  have hcd : ∀ t, Dense {a | C t a} := by
    rintro (t | t)
    · exact dense_mixed_independent P b (e ∘ v₁ t) (he₁ t) (fun i ↦ A (v₁ t i)) (hf₁ t) (hc₁ t)
    · exact dense_mixed_augmented P b (e ∘ v₂ t) (he₂ t) (fun i ↦ A (v₂ t i)) (hf₂ t) (hc₂ t)
  have hd := dense_finite_conditions C hco hcd
  let U : Set ({q // ¬ P q} → V) :=
    {a | dist (mixedVertexEvaluation P b e A a) (fun w ↦ A w (b (e w))) < ε}
  have hU : IsOpen U := isOpen_lt
    ((mixedVertexEvaluation_continuous P b e A).dist continuous_const) continuous_const
  have hUn : U.Nonempty := by
    refine ⟨fun q ↦ b q.val, ?_⟩
    have heq : mixedVertexEvaluation P b e A (fun q ↦ b q.val) = (fun w ↦ A w (b (e w))) := by
      funext w
      simp only [mixedVertexEvaluation]
      split_ifs <;> rfl
    change dist _ _ < ε
    rw [heq, dist_self]
    exact hε
  obtain ⟨a, hau, ha⟩ := hd.inter_open_nonempty U hU hUn
  refine ⟨a, ?_, ?_, ?_⟩
  · exact (dist_pi_lt_iff hε).mp hau
  · intro t
    exact ha (Sum.inl t)
  · intro t
    exact ha (Sum.inr t)

end SharpLiebThirring.PLParity

end
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


namespace SharpLiebThirring.PLParity
section EquivariantAssignment
variable {G : Type u95} {X : Type u96} [Group G] [MulAction G X] [IsCancelSMul G X]

lemma assignment_reconstruct (x : X) : orbitTransport (G := G) x • (orbitLabel (G := G) x).out = x :=
  assignmentEquiv.apply_symm_apply x

lemma assignment_symm_smul (g : G) (x : X) :
    assignmentEquiv.symm (g • x) = (orbitLabel (G := G) x, g * orbitTransport x) := by
  apply assignmentEquiv.injective
  rw [Equiv.apply_symm_apply]
  change g • x = (g * orbitTransport x) • (orbitLabel (G := G) x).out
  rw [mul_smul, assignment_reconstruct]

lemma orbitLabel_smul (g : G) (x : X) : orbitLabel (G := G) (g • x) = orbitLabel x := by
  simpa only [orbitLabel] using congrArg Prod.fst (assignment_symm_smul g x)

lemma orbitTransport_smul (g : G) (x : X) : orbitTransport (g • x) = g * orbitTransport x :=
  congrArg Prod.snd (assignment_symm_smul g x)

lemma orbitLabel_eq_mk (x : X) : orbitLabel (G := G) x = Quotient.mk'' x := by
  have h := assignment_orbit_smul (orbitTransport (G := G) x) (orbitLabel (G := G) x).out
  rw [assignment_reconstruct, Quotient.out_eq'] at h
  exact h.symm

variable {V : Type u97} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : G →* (V ≃ₗ[ℝ] V))

omit [FiniteDimensional ℝ V] in
lemma equivariantAssignment_smul (a : Orbit (G := G) (X := X) → V) (g : G) (x : X) :
    equivariantAssignment ρ a (g • x) = ρ g (equivariantAssignment ρ a x) := by
  simp only [equivariantAssignment, orbitLabel_smul, orbitTransport_smul, map_mul,
    LinearEquiv.mul_apply]

omit [FiniteDimensional ℝ V] in
lemma equivariantAssignment_recovers (b : X → V)
    (hb : ∀ g : G, ∀ x, b (g • x) = ρ g (b x)) (x : X) :
    ρ (orbitTransport x) (b (orbitLabel (G := G) x).out) = b x := by
  rw [← hb, assignment_reconstruct]

/-- Free finite group actions admit arbitrarily close equivariant generic
vertex values, while retaining a prescribed invariant family exactly. -/
lemma exists_equivariant_generic [Fintype X]
    {T₁ : Type u98} {T₂ : Type u99} [Fintype T₁] [Fintype T₂]
    (J₁ : T₁ → Type u193) (J₂ : T₂ → Type u194) [∀ t, Fintype (J₁ t)] [∀ t, Fintype (J₂ t)]
    (P : X → Prop) (hP : ∀ g : G, ∀ x, P (g • x) ↔ P x)
    (b : X → V) (hb : ∀ g : G, ∀ x, b (g • x) = ρ g (b x))
    (v₁ : ∀ t, J₁ t → X) (v₂ : ∀ t, J₂ t → X)
    (he₁ : ∀ t, Function.Injective (orbitLabel (G := G) ∘ v₁ t))
    (he₂ : ∀ t, Function.Injective (orbitLabel (G := G) ∘ v₂ t))
    (hf₁ : ∀ t, LinearIndependent ℝ (fun i : {i // P (v₁ t i)} ↦ b (v₁ t i.val)))
    (hf₂ : ∀ t, LinearIndependent ℝ (fun i : {i // P (v₂ t i)} ↦ ((1 : ℝ), b (v₂ t i.val))))
    (hc₁ : ∀ t, Fintype.card (J₁ t) ≤ Module.finrank ℝ V)
    (hc₂ : ∀ t, Fintype.card (J₂ t) ≤ Module.finrank ℝ V + 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : X → V,
      (∀ g : G, ∀ x, a (g • x) = ρ g (a x)) ∧
      (∀ x, dist (a x) (b x) < ε) ∧
      (∀ x, P x → a x = b x) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ a (v₁ t i))) ∧
      (∀ t, LinearIndependent ℝ (fun i ↦ ((1 : ℝ), a (v₂ t i)))) := by
  classical
  let Q := Orbit (G := G) (X := X)
  let P' : Q → Prop := fun q ↦ P q.out
  let b' : Q → V := fun q ↦ b q.out
  let e : X → Q := orbitLabel (G := G)
  let A : X → V ≃ₗ[ℝ] V := fun x ↦ ρ (orbitTransport x)
  have hpe (x : X) : P' (e x) ↔ P x := by
    change P (orbitLabel (G := G) x).out ↔ P x
    have h := hP (orbitTransport (G := G) x) (orbitLabel (G := G) x).out
    rw [assignment_reconstruct] at h
    exact h.symm
  have hbe (x : X) : A x (b' (e x)) = b x := equivariantAssignment_recovers ρ b hb x
  have hfix₁ (t : T₁) : LinearIndependent ℝ
      (fun i : {i // P' (e (v₁ t i))} ↦ A (v₁ t i.val) (b' (e (v₁ t i.val)))) := by
    simp only [hbe]
    exact (hf₁ t).comp (fun i : {i // P' (e (v₁ t i))} ↦ ⟨i.val, (hpe _).mp i.prop⟩)
      (by
        intro i j h
        apply Subtype.ext
        exact congrArg (fun z : {i // P (v₁ t i)} ↦ z.val) h)
  have hfix₂ (t : T₂) : LinearIndependent ℝ
      (fun i : {i // P' (e (v₂ t i))} ↦ ((1 : ℝ), A (v₂ t i.val) (b' (e (v₂ t i.val))))) := by
    simp only [hbe]
    exact (hf₂ t).comp (fun i : {i // P' (e (v₂ t i))} ↦ ⟨i.val, (hpe _).mp i.prop⟩)
      (by
        intro i j h
        apply Subtype.ext
        exact congrArg (fun z : {i // P (v₂ t i)} ↦ z.val) h)
  obtain ⟨c, hc, h₁, h₂⟩ := exists_mixed_generic J₁ J₂ P' b' e A v₁ v₂
    he₁ he₂ hfix₁ hfix₂ hc₁ hc₂ ε hε
  let a' : Q → V := fun q ↦ if h : P' q then b' q else c ⟨q, h⟩
  let a : X → V := equivariantAssignment ρ a'
  have ha (x : X) : a x = mixedVertexEvaluation P' b' e A c x := rfl
  refine ⟨a, equivariantAssignment_smul ρ a', ?_, ?_, ?_, ?_⟩
  · intro x
    rw [ha, ← hbe]
    exact hc x
  · intro x hx
    rw [ha]
    simp only [mixedVertexEvaluation, dite_eq_left ((hpe x).mpr hx), hbe]
  · simpa only [← ha] using h₁
  · simpa only [← ha] using h₂

end EquivariantAssignment
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open SharpLiebThirring.PLParity
open Finset
attribute [local instance] Classical.propDecidable

lemma card_omit_one_le {n : ℕ} (i : Fin (n + 1)) : Fintype.card {k // k ≠ i} ≤ n := by
  have h := Fintype.card_subtype_lt (p := fun k : Fin (n + 1) ↦ k ≠ i) (x := i) (by simp)
  simp only [Fintype.card_fin] at h
  omega

lemma card_omit_two_le {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    Fintype.card {k // k ≠ i ∧ k ≠ j} + 1 ≤ n := by
  let e : {k // k ≠ i ∧ k ≠ j} ≃ {k : {k : Fin (n + 1) // k ≠ i} // k.val ≠ j} :=
    ⟨fun k ↦ ⟨⟨k.val, k.prop.1⟩, k.prop.2⟩, fun k ↦ ⟨k.val.val, k.val.prop, k.prop⟩,
      by intro k; rfl, by intro k; rfl⟩
  have hc := Fintype.card_congr e
  have hl := Fintype.card_subtype_lt (p := fun k : {k : Fin (n + 1) // k ≠ i} ↦ k.val ≠ j)
    (x := ⟨j, hij.symm⟩) (by simp)
  have hu := card_omit_one_le i
  omega

/-- General position on all facets of an invariant finite cubical complex,
retaining an already independent invariant part of its vertex data. -/
lemma generic_on_complex {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    [Fintype D] [IsCancelSMul H (vertices H D)]
    {V : Type u100} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (hc : n = Module.finrank ℝ V + 1)
    (P : vertices H D → Prop) (hP : ∀ s : H, ∀ z, P (s • z) ↔ P z)
    (b : vertices H D → V) (hb : ∀ s : H, ∀ z, b (s • z) = ρ s (b z))
    (haug : ∀ F : D, ∀ j : Fin (n + 1), LinearIndependent ℝ
      (fun k : {k : {k : Fin (n + 1) // k ≠ j} // P (flagVertex H D F k.val)} ↦
        ((1 : ℝ), b (flagVertex H D F k.val.val))))
    (hvec : ∀ F : D, ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
      (fun k : {k : {k : Fin (n + 1) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
        b (flagVertex H D F k.val.val)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : vertices H D → V,
      (∀ s : H, ∀ z, a (s • z) = ρ s (a z)) ∧
      (∀ z, dist (a z) (b z) < ε) ∧
      (∀ z, P z → a z = b z) ∧
      (∀ F : D, ∀ j : Fin (n + 1), LinearIndependent ℝ
        (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k)))) ∧
      (∀ F : D, ∀ i j : Fin (n + 1), i ≠ j → LinearIndependent ℝ
        (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k))) := by
  classical
  let T₁ := D × {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2}
  let T₂ := D × Fin (n + 1)
  let J₁ (t : T₁) := {k // k ≠ t.2.val.1 ∧ k ≠ t.2.val.2}
  let J₂ (t : T₂) := {k // k ≠ t.2}
  let v₁ (t : T₁) (k : J₁ t) := flagVertex H D t.1 k.val
  let v₂ (t : T₂) (k : J₂ t) := flagVertex H D t.1 k.val
  have hi₁ (t : T₁) : Function.Injective (orbitLabel (G := H) ∘ v₁ t) := by
    intro k l he
    simp only [Function.comp_apply, orbitLabel_eq_mk] at he
    exact Subtype.ext (flagVertex_orbits_injective H D t.1 he)
  have hi₂ (t : T₂) : Function.Injective (orbitLabel (G := H) ∘ v₂ t) := by
    intro k l he
    simp only [Function.comp_apply, orbitLabel_eq_mk] at he
    exact Subtype.ext (flagVertex_orbits_injective H D t.1 he)
  obtain ⟨a, ha, he, hp, hv, hu⟩ := exists_equivariant_generic ρ J₁ J₂ P hP b hb v₁ v₂
    hi₁ hi₂ (fun t ↦ hvec t.1 _ _ t.2.prop) (fun t ↦ haug t.1 t.2)
    (fun t ↦ by
      change Fintype.card {k // k ≠ t.2.val.1 ∧ k ≠ t.2.val.2} ≤ _
      have hk := card_omit_two_le t.2.val.1 t.2.val.2 t.2.prop
      omega)
    (fun t ↦ by
      change Fintype.card {k // k ≠ t.2} ≤ _
      have hk := card_omit_one_le t.2
      omega) ε hε
  refine ⟨a, ha, he, hp, ?_, ?_⟩
  · intro F j
    exact hu (F,j)
  · intro F i j hij
    exact hv (F,⟨(i,j),hij⟩)

end SharpLiebThirring.CubeFlags


namespace SharpLiebThirring.CubeFlags
open Finset

lemma embed_spatial_of_time_zero {d : ℕ} (x : Fin (d + 1) → ℝ) (hx : x (Fin.last d) = 0) :
    embedSpatial (spatial x) = x := by
  change Fin.snoc (Fin.init x) 0 = x
  rw [← hx, Fin.snoc_init_self]

lemma augmented_spatial_independent {d : ℕ} {ι : Type u101} (v : ι → Fin (d + 1) → ℝ)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i)))
    (ht : ∀ i, v i (Fin.last d) = 0) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), spatial (v i))) := by
  let L : (ℝ × (Fin d → ℝ)) →ₗ[ℝ] (ℝ × (Fin (d + 1) → ℝ)) :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap embedSpatial
  have he : (fun i ↦ L ((1 : ℝ), spatial (v i))) = (fun i ↦ ((1 : ℝ), v i)) := by
    funext i
    exact Prod.ext rfl (embed_spatial_of_time_zero (v i) (ht i))
  apply LinearIndependent.of_comp L
  change LinearIndependent ℝ (fun i ↦ L ((1 : ℝ), spatial (v i)))
  rw [he]
  exact hv

lemma augmented_scale_independent {d : ℕ} {ι : Type u102} (v : ι → Fin d → ℝ)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) {h : ℝ} (hh : h ≠ 0) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), h • v i)) := by
  let L : (ℝ × (Fin d → ℝ)) →ₗ[ℝ] (ℝ × (Fin d → ℝ)) :=
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prodMap (h • LinearMap.id)
  have hL : Function.Injective L := by
    rintro ⟨a,x⟩ ⟨b,y⟩ he
    have hab := congrArg Prod.fst he
    have hxy : h • x = h • y := congrArg Prod.snd he
    exact Prod.ext hab ((smul_right_injective _ hh) hxy)
  exact hv.map' L (LinearMap.ker_eq_bot.mpr hL)

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

lemma orbitBall_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    g • x ∈ orbitBall (G := G) p R := by
  obtain ⟨k,hk⟩ := hx
  refine ⟨g*k, ?_⟩
  rw [mul_smul, dist_smul]
  exact hk

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

include hR hsep in
lemma ballLabel_smul (g : G) {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    ballLabel (G := G) p R (g • x) = g * ballLabel (G := G) p R x := by
  apply ballLabel_eq p R hR hsep
  rw [mul_smul, dist_smul]
  exact ballLabel_dist p R hx

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq_of_dist {x y : E} (hx : x ∈ orbitBall (G := G) p R)
    (hy : y ∈ orbitBall (G := G) p R) (hxy : dist x y ≤ R) :
    ballLabel (G := G) p R x = ballLabel (G := G) p R y := by
  by_contra hn
  have hlx := ballLabel_dist p R hx
  have hly := ballLabel_dist p R hy
  have hd := dist_triangle4 (ballLabel (G := G) p R x • p) x y (ballLabel (G := G) p R y • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

include hR hsep in
omit [IsIsometricSMul G E] in
lemma exists_common_ballLabel {ι : Type u105} (v : ι → E) (P : ι → Prop)
    (hv : ∀ i, P i → v i ∈ orbitBall (G := G) p R)
    (hd : ∀ i j, dist (v i) (v j) ≤ R) :
    ∃ g : G, ∀ i, P i → ballLabel (G := G) p R (v i) = g := by
  by_cases hn : ∃ i, P i
  · obtain ⟨j,hj⟩ := hn
    refine ⟨ballLabel (G := G) p R (v j), ?_⟩
    intro i hi
    exact ballLabel_eq_of_dist p R hR hsep (hv i hi) (hv j hj) (hd i j)
  · exact ⟨1, fun i hi ↦ False.elim (hn ⟨i,hi⟩)⟩

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section Translate
variable {V : Type u106} {W : Type u107} {ι : Type u108} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
lemma augmented_translate_independent (v : ι → V) (p : V)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i - p)) := by
  let fst : (ℝ × V) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ V
  let snd : (ℝ × V) →ₗ[ℝ] V := LinearMap.snd ℝ ℝ V
  let T : (ℝ × V) →ₗ[ℝ] (ℝ × V) := fst.prod (snd - fst.smulRight p)
  have hT : Function.Injective T := by
    rintro ⟨a,x⟩ ⟨b,y⟩ he
    have hab : a = b := congrArg Prod.fst he
    have hxy : x - a • p = y - b • p := congrArg Prod.snd he
    rw [← hab] at hxy
    exact Prod.ext hab (sub_left_inj.mp hxy)
  have hh := hv.map' T (LinearMap.ker_eq_bot.mpr hT)
  change LinearIndependent ℝ (fun i ↦ T ((1 : ℝ), v i)) at hh
  have he : (fun i ↦ T ((1 : ℝ), v i)) = (fun i ↦ ((1 : ℝ), v i - p)) := by
    funext i
    change ((1 : ℝ), v i - (1 : ℝ) • p) = (1, v i - p)
    rw [one_smul]
  rwa [he] at hh

lemma augmented_equiv_independent (v : ι → V) (L : V ≃ₗ[ℝ] W)
    (hv : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), v i))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), L (v i))) :=
  hv.map' ((LinearEquiv.refl ℝ ℝ).prodCongr L).toLinearMap
    (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))
end Translate

lemma Signs.smul_time_zero {d : ℕ} (s : Signs (d + 1)) (x : Fin (d + 1) → ℝ)
    (hx : x (Fin.last d) = 0) : (s • x) (Fin.last d) = 0 := by
  simp only [Signs.smul_real, hx, neg_zero, ite_self]

lemma Flag.augmented_spatial_scaled {d : ℕ} {ι : Type u109} (F : Flag (d + 1))
    (v : ι → Fin (d + 2)) (hv : Function.Injective v) {h : ℝ} (hh : h ≠ 0)
    (s : Signs (d + 1)) (ht : ∀ i, (h • F.point (v i)) (Fin.last d) = 0) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), spatial (s • (h • F.point (v i))))) := by
  have hu := augmented_scale_independent (fun i ↦ F.point (v i))
    (F.augmented_linearIndependent.comp v hv) hh
  have hr := augmented_equiv_independent (fun i ↦ h • F.point (v i))
    s.linearIsometry.toLinearEquiv hu
  exact augmented_spatial_independent _ hr (fun i ↦ s.smul_time_zero _ (ht i))

section Model
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u110} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin (d + 1) → ℝ) (R : ℝ)

lemma affineOrbitModel_smul (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (q : Fin d → ℝ) (s : H) {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) p R) :
    affineOrbitModel H ρ L p R q (s • x) = ρ s (affineOrbitModel H ρ L p R q x) := by
  simp only [affineOrbitModel, ballLabel_smul p R hR hsep s hx, mul_inv_rev,
    mul_smul, inv_smul_smul, map_mul, LinearEquiv.mul_apply]

lemma affineOrbitModel_dist (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (q q' : Fin d → ℝ) (x : Fin (d + 1) → ℝ) :
    dist (affineOrbitModel H ρ L p R q x) (affineOrbitModel H ρ L p R q' x) = dist (L q) (L q') := by
  let s := ballLabel (G := H) p R x
  simp only [dist_eq_norm, affineOrbitModel, ← map_sub, hρ]
  have he : spatial (s⁻¹ • x) - q - (spatial (s⁻¹ • x) - q') = q' - q := by abel
  change ‖L (spatial (s⁻¹ • x) - q - (spatial (s⁻¹ • x) - q'))‖ = ‖L (q - q')‖
  rw [he, map_sub, map_sub, norm_sub_rev]

lemma affineOrbitModel_augmented {ι : Type u111} (q : Fin d → ℝ)
    (x : ι → Fin (d + 1) → ℝ) (s : H)
    (hs : ∀ i, ballLabel (G := H) p R (x i) = s)
    (hi : LinearIndependent ℝ (fun i ↦ ((1 : ℝ), spatial (s⁻¹ • x i)))) :
    LinearIndependent ℝ (fun i ↦ ((1 : ℝ), affineOrbitModel H ρ L p R q (x i))) := by
  simp only [affineOrbitModel, hs]
  exact augmented_equiv_independent _ (L.trans (ρ s)) (augmented_translate_independent _ q hi)

lemma affineOrbitModel_independent {ι : Type u112} (q : Fin d → ℝ)
    (x : ι → Fin (d + 1) → ℝ) (s : H)
    (hs : ∀ i, ballLabel (G := H) p R (x i) = s)
    (hi : LinearIndependent ℝ (fun i ↦ spatial (s⁻¹ • x i) - q)) :
    LinearIndependent ℝ (fun i ↦ affineOrbitModel H ρ L p R q (x i)) := by
  simp only [affineOrbitModel, hs]
  exact hi.map' (L.trans (ρ s)).toLinearMap (LinearMap.ker_eq_bot.mpr (LinearEquiv.injective _))

end Model
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

lemma Flag.dist_gridPoint_gridPoint {n : ℕ} (F : Flag n) (h : ℝ) (hh : 0 ≤ h)
    (j k : Fin (n + 1)) : dist (gridPoint h (F.vertex j)) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, gridPoint_vertex]
  calc
    _ ≤ dist (h • F.point j) (h • F.center) + dist (h • F.center) (h • F.point k) := dist_triangle _ _ _
    _ ≤ h / 2 + h / 2 := by
      apply add_le_add (F.dist_scaled_point_center h hh j)
      rw [dist_comm]
      exact F.dist_scaled_point_center h hh k
    _ = h := by ring

lemma exists_generic_initial_root {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1))) [Fintype D]
    (h : ℝ) (hh : h ≠ 0) (P : vertices H D → Prop)
    (hP : ∀ z : vertices H D, P z → gridPoint h z.val (Fin.last d) = 0)
    (U : Set (Fin d → ℝ)) (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ q ∈ U, ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → ∀ s : H,
      LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} //
          P (flagVertex H D F k.val)} ↦
        spatial (s⁻¹ • gridPoint h (F.val.vertex k.val.val)) - q) := by
  classical
  let T := (D × {p : Fin (d + 2) × Fin (d + 2) // p.1 ≠ p.2}) × H
  let J (t : T) := {k : {k : Fin (d + 2) // k ≠ t.1.2.val.1 ∧ k ≠ t.1.2.val.2} //
    P (flagVertex H D t.1.1 k.val)}
  let v (t : T) (k : J t) := spatial (t.2⁻¹ • gridPoint h (t.1.1.val.vertex k.val.val))
  have hv (t : T) : LinearIndependent ℝ (fun k ↦ ((1 : ℝ), v t k)) := by
    have hh' := t.1.1.val.augmented_spatial_scaled (fun k : J t ↦ k.val.val)
      (fun _ _ he ↦ Subtype.ext (Subtype.ext he)) hh t.2⁻¹.val (fun k ↦ by
        rw [← gridPoint_vertex]
        exact hP (flagVertex H D t.1.1 k.val.val) k.prop)
    simpa only [v, gridPoint_vertex, Subgroup.smul_def] using hh'
  have hc (t : T) : Fintype.card (J t) ≤ Module.finrank ℝ (Fin d → ℝ) := by
    have h₁ := Fintype.card_subtype_le (fun k : {k : Fin (d + 2) // k ≠ t.1.2.val.1 ∧ k ≠ t.1.2.val.2} ↦
      P (flagVertex H D t.1.1 k.val))
    have h₂ := card_omit_two_le t.1.2.val.1 t.1.2.val.2 t.1.2.prop
    change Fintype.card (J t) ≤ _ at h₁
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact h₁.trans (Nat.le_of_succ_le_succ h₂)
  have hd := dense_finite_conditions (fun t : T ↦ fun q : Fin d → ℝ ↦
      LinearIndependent ℝ (fun k ↦ v t k - q))
    (fun t ↦ isOpen_independent_shift (v t)) (fun t ↦ dense_independent_shift (v t) (hv t) (hc t))
  obtain ⟨q,hqu,hq⟩ := hd.inter_open_nonempty U hU hUn
  exact ⟨q,hqu,fun F i j hij s ↦ hq ((F,⟨(i,j),hij⟩),s)⟩

lemma common_flag_label {d : ℕ} (H : Subgroup (Signs (d + 1)))
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (F : Flag (d + 1)) (P : Fin (d + 2) → Prop)
    (hb : ∀ k, P k → gridPoint h (F.vertex k) ∈ orbitBall (G := H) p R) :
    ∃ s : H, ∀ k, P k → ballLabel (G := H) p R (gridPoint h (F.vertex k)) = s := by
  have hd : ∀ i j : Fin (d + 2),
      dist (gridPoint h (F.vertex i)) (gridPoint h (F.vertex j)) ≤ R :=
    fun i j ↦ (F.dist_gridPoint_gridPoint h hh.le i j).trans hhr
  exact exists_common_ballLabel (G := H) p R hR hsep
    (fun k : Fin (d + 2) ↦ gridPoint h (F.vertex k)) P hb hd

lemma fixed_initial_augmented {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    {V : Type u113} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (P : vertices H D → Prop)
    (ht : ∀ z : vertices H D, P z → gridPoint h z.val (Fin.last d) = 0)
    (hb : ∀ z : vertices H D, P z → gridPoint h z.val ∈ orbitBall (G := H) p R)
    (q : Fin d → ℝ) (F : D) (j : Fin (d + 2)) :
    LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
      ((1 : ℝ), affineOrbitModel H ρ L p R q (gridPoint h (F.val.vertex k.val.val)))) := by
  obtain ⟨s,hs⟩ := common_flag_label H p R h hR hh hhr hsep
    F.val (fun k ↦ P (flagVertex H D F k)) (fun k hk ↦ hb (flagVertex H D F k) hk)
  apply affineOrbitModel_augmented H ρ L p R q
    (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
      gridPoint h (F.val.vertex k.val.val)) s (fun k ↦ hs k.val.val k.prop)
  have hu := F.val.augmented_spatial_scaled
    (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦ k.val.val)
    (fun _ _ he ↦ Subtype.ext (Subtype.ext he)) hh.ne' s⁻¹.val (fun k ↦ by
      rw [← gridPoint_vertex]
      exact ht (flagVertex H D F k.val.val) k.prop)
  simpa only [gridPoint_vertex, Subgroup.smul_def] using hu

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma dist_convex_sum_le {ι : Type u114} {E : Type u115} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (x : ι → E) (p : E) (r : ℝ)
    (hx : ∀ i, dist (x i) p ≤ r) : dist (∑ i, w i • x i) p ≤ r := by
  have he : (∑ i, w i • x i) - p = ∑ i, w i • (x i - p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]
  rw [dist_eq_norm, he]
  calc
    _ ≤ ∑ i, ‖w i • (x i - p)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * r := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hx i) (hw i)
    _ = r := by rw [← Finset.sum_mul, hs, one_mul]

/-- The bottom cube has a nonempty open family of roots with strictly positive
facet barycentric coordinates. A generic root can be chosen in this family. -/
lemma bottomSeed_open_roots {d : ℕ} (h : ℝ) (hh : 0 < h) (p : Fin d → ℝ) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, ∃ w : Fin (d + 2) → ℝ,
        (∀ k, 0 ≤ w k) ∧ (∀ k, k ≠ Fin.last (d + 1) → 0 < w k) ∧
        ∑ k, w k = 1 ∧ w (Fin.last (d + 1)) = 0 ∧
        ∑ k, w k • gridPoint h ((bottomSeed h p).vertex k) = embedSpatial q ∧
        dist (embedSpatial q) (embedSpatial p) ≤ 2 * h := by
  classical
  let F := bottomSeed h p
  let v : Fin (d + 1) → Fin d → ℝ := fun k ↦ spatial (h • F.point k.castSucc)
  have hv : LinearIndependent ℝ (fun k ↦ ((1 : ℝ), v k)) := by
    have hi := F.augmented_spatial_scaled Fin.castSucc (Fin.castSucc_injective _) hh.ne' 1
      (fun k ↦ by
        change h * F.point k.castSucc (Fin.last d) = 0
        rw [bottomSeed_time h p _ (Fin.castSucc_ne_last k), mul_zero])
    simpa only [one_smul] using hi
  let w₀ : Fin (d + 1) → ℝ := fun _ ↦ (d + 1 : ℝ)⁻¹
  have hw₀ : ∀ k, 0 < w₀ k := fun _ ↦ by dsimp [w₀]; positivity
  have hs₀ : ∑ k, w₀ k = 1 := by
    simp only [w₀, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ (by positivity)
  obtain ⟨U,hU,hq₀,hpos⟩ := positive_barycentric_neighborhood v hv (by simp) w₀ hw₀ hs₀
  refine ⟨U,hU,⟨_,hq₀⟩,?_⟩
  intro q hq
  obtain ⟨z,hz,hzs,he⟩ := hpos q hq
  let w : Fin (d + 2) → ℝ := Fin.snoc z 0
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simp [w]
    · simpa only [w,Fin.snoc_castSucc] using (hz j).le
  have hp : ∀ k, k ≠ Fin.last (d + 1) → 0 < w k := by
    intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · exact fun hk ↦ False.elim (hk rfl)
    · intro _
      simpa only [w,Fin.snoc_castSucc] using hz j
  have hs : ∑ k, w k = 1 := by
    rw [Fin.sum_univ_castSucc]
    simpa only [w,Fin.snoc_castSucc,Fin.snoc_last,add_zero] using hzs
  have hlast : w (Fin.last (d + 1)) = 0 := Fin.snoc_last _ _
  have hgrid (k : Fin (d + 1)) : gridPoint h (F.vertex k.castSucc) = embedSpatial (v k) := by
    rw [gridPoint_vertex]
    apply (embed_spatial_of_time_zero _ ?_).symm
    change h * F.point k.castSucc (Fin.last d) = 0
    rw [bottomSeed_time h p _ (Fin.castSucc_ne_last k), mul_zero]
  have hsum : ∑ k, w k • gridPoint h (F.vertex k) = embedSpatial q := by
    rw [Fin.sum_univ_castSucc]
    simp only [w, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, hgrid]
    rw [← he, map_sum]
    exact Finset.sum_congr rfl (fun k _ ↦ (map_smul embedSpatial (z k) (v k)).symm)
  refine ⟨w,hw,hp,hs,hlast,hsum,?_⟩
  rw [← hsum]
  apply dist_convex_sum_le w hw hs _ _ _
  intro k
  rw [gridPoint_vertex]
  exact bottomSeed_dist_point h hh p k

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
namespace SharpLiebThirring.PLParity

section Compactness
variable {E : Type u116} {V : Type u117} [TopologicalSpace E] [NormedAddCommGroup V]

/-- On a compact domain, sufficiently small values lie in any open neighborhood
of the zero set. This is not an existence assumption about zeros. -/
lemma small_norm_near_zeros {C U : Set E} (hC : IsCompact C) (hU : IsOpen U)
    (f : E → V) (hf : ContinuousOn f C) (hzero : ∀ x ∈ C, f x = 0 → x ∈ U) :
    ∃ ε > 0, ∀ x ∈ C, ‖f x‖ < ε → x ∈ U := by
  by_cases hn : (C \ U).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (hC.diff hU).exists_isMinOn hn (hf.norm.mono sdiff_subset)
    have hp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun h ↦ hx.2 (hzero x hx.1 h))
    refine ⟨‖f x‖, hp, ?_⟩
    intro y hy hfy
    by_contra hu
    exact (not_lt_of_ge (hmin ⟨hy, hu⟩)) hfy
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _
    by_contra hu
    exact hn ⟨x, hx, hu⟩
end Compactness

section ConvexError
variable {ι : Type u118} {V : Type u119} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_of_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (a : ι → V) (ha : ∑ i, w i • a i = 0) (z : V) (ε : ℝ)
    (he : ∀ i, ‖a i - z‖ ≤ ε) : ‖z‖ ≤ ε := by
  have hid : ∑ i, w i • (a i - z) = -z := by
    simp only [smul_sub, Finset.sum_sub_distrib, ha, ← Finset.sum_smul, hs, one_smul, zero_sub]
  calc
    ‖z‖ = ‖∑ i, w i • (a i - z)‖ := by rw [hid, norm_neg]
    _ ≤ ∑ i, ‖w i • (a i - z)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_left (he i) (hw i)
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

lemma norm_of_approximate_convex_zero (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (a b : ι → V) (ha : ∑ i, w i • a i = 0)
    (z : V) (ε δ : ℝ) (he : ∀ i, dist (a i) (b i) ≤ ε)
    (hd : ∀ i, dist (b i) z ≤ δ) : ‖z‖ ≤ ε + δ := by
  apply norm_of_convex_zero w hw hs a ha z (ε + δ)
  intro i
  rw [← dist_eq_norm]
  exact (dist_triangle _ _ _).trans (add_le_add (he i) (hd i))
end ConvexError

section FreeLocus
variable {G : Type u120} {E : Type u121} [Group G] [MulAction G E]

variable [TopologicalSpace E] [T2Space E] [ContinuousConstSMul G E] [Finite G]

lemma isOpen_freeLocus : IsOpen (freeLocus (G := G) (E := E)) := by
  classical
  have hset : freeLocus (G := G) (E := E) = ⋂ g : {g : G // g ≠ 1}, {x | g.val • x ≠ x} := by
    ext x
    simp only [freeLocus, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h ⟨g, hg⟩ he
      exact hg (h g he)
    · intro h g hg
      by_contra hn
      exact h ⟨g, hn⟩ hg
  rw [hset]
  apply isOpen_iInter_of_finite
  intro g
  exact (isClosed_eq (continuous_const_smul g.val) continuous_id).isOpen_compl

end FreeLocus
section FreeTube
variable {G : Type u122} {E : Type u123} [Group G] [MulAction G E] [MetricSpace E]
  [ContinuousConstSMul G E] [Finite G]

lemma compact_free_tube {K : Set E}
    (hK : IsCompact K) (hfree : K ⊆ freeLocus (G := G)) :
    ∃ r > 0, Metric.cthickening r K ⊆ freeLocus (G := G) :=
  hK.exists_cthickening_subset_open isOpen_freeLocus hfree

end FreeTube
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Flag.combination_neighbor {n : ℕ} [NeZero n] (h : ℝ) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (hj : w j = 0) :
    (F.neighbor j).combination h w = F.combination h w := by
  unfold combination
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j
  · simp only [hk, hj, zero_smul]
  · have he : (F.neighbor j).point k = F.point k := by
      ext i
      simp only [point, congrFun (F.neighbor_vertex j k hk) i]
    rw [he]

lemma Flag.dist_combination_scaled_center {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    dist (F.combination h w) (h • F.center) ≤ h / 2 := by
  rw [combination, dist_scale h hh]
  nlinarith [F.dist_combination_center w hw hs]

lemma Flag.dist_combination_gridPoint {n : ℕ} (h : ℝ) (hh : 0 ≤ h) (F : Flag n)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (k : Fin (n + 1)) :
    dist (F.combination h w) (gridPoint h (F.vertex k)) ≤ h := by
  rw [gridPoint_vertex, combination, dist_scale h hh]
  nlinarith [F.dist_combination_point w hw hs k]

lemma nearCylinder_combination_cthickening {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ)
    (hh : 0 ≤ h) (t : Fin n) (m : ℕ) {F : Flag n} (hF : F ∈ nearCylinder K h r t m)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    F.combination h w ∈ Metric.cthickening (r + h / 2) K := by
  obtain ⟨x, hx, hd⟩ := hF.1
  apply Metric.mem_cthickening_of_dist_le _ x _ K hx
  calc
    _ ≤ dist (F.combination h w) (h • F.center) + dist (h • F.center) x := dist_triangle _ _ _
    _ ≤ h / 2 + r := add_le_add (F.dist_combination_scaled_center h hh w hw hs) hd.le
    _ = r + h / 2 := add_comm _ _

/-- A PL zero gives a small value of the continuous map at its geometric point. -/
lemma norm_at_mesh_zero {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
    {V : Type u125} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : vertices H D → V) (f : (Fin n → ℝ) → V) (h ε δ : ℝ) (hh : 0 ≤ h)
    (C : Set (Fin n → ℝ))
    (ha : ∀ z : vertices H D, dist (a z) (f (gridPoint h z.val)) ≤ ε)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ h → dist (f x) (f y) ≤ δ)
    (F : D) (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hz : ∑ k, w k • a (flagVertex H D F k) = 0)
    (hC : F.val.combination h w ∈ C)
    (hp : ∀ k, gridPoint h (F.val.vertex k) ∈ C) :
    ‖f (F.val.combination h w)‖ ≤ ε + δ := by
  apply norm_of_approximate_convex_zero w hw hs (fun k ↦ a (flagVertex H D F k))
    (fun k ↦ f (gridPoint h (F.val.vertex k))) hz (f (F.val.combination h w)) ε δ
  · intro k
    exact ha (flagVertex H D F k)
  · intro k
    exact hf _ (hp k) _ hC (by
      rw [dist_comm]
      exact F.val.dist_combination_gridPoint h hh w hw hs k)

lemma neighbor_near_centers_of_combination {n : ℕ} [NeZero n]
    (K : Set (Fin n → ℝ)) (h r : ℝ) (hh : 0 ≤ h) (hhr : h < r)
    (F : Flag n) (j : Fin (n + 1))
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (hx : ∃ x ∈ K, dist (F.combination h w) x < r / 2) :
    ∃ x ∈ K, dist (h • (F.neighbor j).center) x < r := by
  obtain ⟨x,hx,hd⟩ := hx
  refine ⟨x,hx,?_⟩
  have hc := (F.neighbor j).dist_combination_scaled_center h hh w hw hs
  rw [F.combination_neighbor h w j hj, dist_comm] at hc
  have ht := dist_triangle (h • (F.neighbor j).center) (F.combination h w) x
  linarith

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
attribute [local instance] Classical.propDecidable

lemma fixed_initial_vectors {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    {V : Type u138} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (p : Fin (d + 1) → ℝ) (R h : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • p) (k • p))
    (P : vertices H D → Prop)
    (hb : ∀ z : vertices H D, P z → gridPoint h z.val ∈ orbitBall (G := H) p R)
    (q : Fin d → ℝ) (F : D) (i j : Fin (d + 2))
    (hq : ∀ s : H, LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
        spatial (s⁻¹ • gridPoint h (F.val.vertex k.val.val)) - q)) :
    LinearIndependent ℝ (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} //
        P (flagVertex H D F k.val)} ↦
      affineOrbitModel H ρ L p R q (gridPoint h (F.val.vertex k.val.val))) := by
  obtain ⟨s,hs⟩ := common_flag_label H p R h hR hh hhr hsep F.val
    (fun k ↦ P (flagVertex H D F k)) (fun k hk ↦ hb (flagVertex H D F k) hk)
  exact affineOrbitModel_independent H ρ L p R q
    (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
      gridPoint h (F.val.vertex k.val.val)) s (fun k ↦ hs k.val.val k.prop) (hq s)

lemma generic_initial_approximation {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (D : SubMulAction H (Flag (d + 1)))
    [Fintype D] [IsCancelSMul H (vertices H D)]
    {V : Type u139} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (R h η : ℝ) (hR : 0 < R) (hh : 0 < h) (hhr : h ≤ R) (hη : 0 < η)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hbnd : ∀ q, dist (embedSpatial q) (embedSpatial p) ≤ 2*h → dist (L q) (L p) < η)
    (f : (Fin (d + 1) → ℝ) → V) (hf : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hmodel : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      f x = affineOrbitModel H ρ L (embedSpatial p) R p x) :
    ∃ (q : Fin d → ℝ) (w : Fin (d + 2) → ℝ) (a : vertices H D → V),
      (∀ k, 0 ≤ w k) ∧ (∀ k, k ≠ Fin.last (d + 1) → 0 < w k) ∧
      ∑ k, w k = 1 ∧ w (Fin.last (d + 1)) = 0 ∧
      (bottomSeed h p).combination h w = embedSpatial q ∧
      (∀ s : H, ∀ z, a (s • z) = ρ s (a z)) ∧
      (∀ z, dist (a z) (f (gridPoint h z.val)) < 2*η) ∧
      (∀ z, gridPoint h z.val (Fin.last d) = 0 →
        gridPoint h z.val ∈ orbitBall (G := H) (embedSpatial p) R →
        a z = affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val)) ∧
      (∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
        (fun k : {k // k ≠ j} ↦ ((1 : ℝ), a (flagVertex H D F k)))) ∧
      (∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
        (fun k : {k // k ≠ i ∧ k ≠ j} ↦ a (flagVertex H D F k))) := by
  classical
  let P : vertices H D → Prop := fun z ↦ gridPoint h z.val (Fin.last d) = 0 ∧
    gridPoint h z.val ∈ orbitBall (G := H) (embedSpatial p) R
  have hP : ∀ s : H, ∀ z, P (s • z) ↔ P z := by
    intro s z
    suffices hs : ∀ s : H, ∀ z, P z → P (s • z) from
      ⟨fun hz ↦ by simpa only [inv_smul_smul] using hs s⁻¹ (s • z) hz, hs s z⟩
    intro s z hz
    change gridPoint h (s.val • z.val) (Fin.last d) = 0 ∧
      gridPoint h (s.val • z.val) ∈ orbitBall (G := H) (embedSpatial p) R
    rw [gridPoint_smul]
    exact ⟨s.val.smul_time_zero _ hz.1, orbitBall_smul (embedSpatial p) R s hz.2⟩
  obtain ⟨U,hU,hUn,hUw⟩ := bottomSeed_open_roots h hh p
  obtain ⟨q,hq,hqg⟩ := exists_generic_initial_root H D h hh.ne' P (fun _ hz ↦ hz.1) U hU hUn
  obtain ⟨w,hw,hwp,hs,hj,he,hd⟩ := hUw q hq
  let b : vertices H D → V := fun z ↦ if P z then
    affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val) else f (gridPoint h z.val)
  have hb : ∀ s : H, ∀ z, b (s • z) = ρ s (b z) := by
    intro s z
    dsimp only [b]
    by_cases hz : P z
    · rw [ite_eq_left hz, ite_eq_left ((hP s z).mpr hz)]
      change affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h (s.val • z.val)) = _
      rw [gridPoint_smul]
      exact affineOrbitModel_smul H ρ L (embedSpatial p) R hR hsep q s hz.2
    · rw [ite_eq_right hz, ite_eq_right (fun hs ↦ hz ((hP s z).mp hs))]
      change f (gridPoint h (s.val • z.val)) = _
      rw [gridPoint_smul]
      exact hf s _
  have hbfix (z : vertices H D) (hz : P z) : b z =
      affineOrbitModel H ρ L (embedSpatial p) R q (gridPoint h z.val) := ite_eq_left hz
  have haug : ∀ F : D, ∀ j : Fin (d + 2), LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ j} // P (flagVertex H D F k.val)} ↦
        ((1 : ℝ), b (flagVertex H D F k.val.val))) := by
    intro F j
    convert fixed_initial_augmented H D ρ L (embedSpatial p) R h hR hh hhr hsep P
      (fun _ hz ↦ hz.1) (fun _ hz ↦ hz.2) q F j using 1
    funext k
    rw [hbfix _ k.prop]
    rfl
  have hvec : ∀ F : D, ∀ i j : Fin (d + 2), i ≠ j → LinearIndependent ℝ
      (fun k : {k : {k : Fin (d + 2) // k ≠ i ∧ k ≠ j} // P (flagVertex H D F k.val)} ↦
        b (flagVertex H D F k.val.val)) := by
    intro F i j hij
    convert fixed_initial_vectors H D ρ L (embedSpatial p) R h hR hh hhr hsep P
      (fun _ hz ↦ hz.2) q F i j (hqg F i j hij) using 1
    funext k
    rw [hbfix _ k.prop]
    rfl
  have hdim : d + 1 = Module.finrank ℝ V + 1 := by
    have hdim := L.finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using congrArg (· + 1) hdim
  obtain ⟨a,ha,hab,haf,hag,hvg⟩ := generic_on_complex H D ρ hdim P hP b hb haug hvec η hη
  refine ⟨q,w,a,hw,hwp,hs,hj,?_,ha,?_,?_,hag,hvg⟩
  · rw [Flag.combination_eq_sum_gridPoint]
    exact he
  · intro z
    have hbf : dist (b z) (f (gridPoint h z.val)) < η := by
      by_cases hz : P z
      · rw [hbfix z hz, hmodel _ hz.1 hz.2, affineOrbitModel_dist H ρ L _ _ hρ]
        exact hbnd q hd
      · simp only [b, ite_eq_right hz, dist_self]
        exact hη
    have ht := dist_triangle (a z) (b z) (f (gridPoint h z.val))
    linarith [hab z]
  · intro z ht hz
    exact (haf z ⟨ht,hz⟩).trans (hbfix z ⟨ht,hz⟩)

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma mesh_boundary_bottom {d : ℕ}
    (K : Set (Fin (d + 1) → ℝ)) (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (m : ℕ) (hm : h * m = 1) (F : Flag (d + 1))
    (hF : F ∈ nearCylinder K h r (Fin.last d) m) (j : Fin (d + 2))
    (hout : F.neighbor j ∉ nearCylinder K h r (Fin.last d) m)
    (w : Fin (d + 2) → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hj : w j = 0)
    (hx : F.combination h w ∈ Metric.thickening (r/2) K)
    (htop : F.combination h w (Fin.last d) < 1) :
    j = Fin.last (d + 1) ∧ (F.order.symm (Fin.last d)).val = d ∧
      F.base (Fin.last d) = 0 ∧ F.corner (Fin.last d) = false := by
  have hn := neighbor_near_centers_of_combination K h r hh.le hhr F j w hw hs hj
    (Metric.mem_thickening_iff.mp hx)
  have hnt : ¬ (0 ≤ (F.neighbor j).base (Fin.last d) ∧
      (F.neighbor j).base (Fin.last d) < (m : ℤ)) :=
    fun ht ↦ hout ⟨hn,ht⟩
  obtain ⟨hjl,ht,hbc⟩ := F.neighbor_outside_time j (Fin.last d) m hF.2.1 hF.2.2 hnt
  refine ⟨hjl,by simpa using ht,?_⟩
  rcases hbc with hbot | htop'
  · exact hbot
  · have hj' : w (Fin.last (d + 1)) = 0 := hjl ▸ hj
    have he := F.combination_time_boundary h (Fin.last d) ht w hs hj'
    simp only [htop'.1, htop'.2, ↓reduceIte, Int.cast_sub, Int.cast_natCast,
      Int.cast_one, sub_add_cancel, hm] at he
    linarith

lemma isOpen_orbitBall {G : Type u140} {E : Type u141} [Group G] [MulAction G E] [MetricSpace E]
    (p : E) (R : ℝ) : IsOpen (orbitBall (G := G) p R) := by
  have he : orbitBall (G := G) p R = ⋃ s : G, Metric.ball (s • p) R := by
    ext x
    simp only [orbitBall, Set.mem_ofPred_eq, Set.mem_iUnion, Metric.mem_ball]
  rw [he]
  exact isOpen_iUnion (fun _ ↦ Metric.isOpen_ball)

lemma exists_positive_mesh (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ h : ℝ, 0 < m ∧ 0 < h ∧ h < δ ∧ h * m = 1 := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n+1,1 / ((n : ℝ)+1), Nat.succ_pos _, by positivity,hn,?_⟩
  push_cast
  exact div_mul_cancel₀ 1 (by positivity)

lemma bottomSeed_mem_nearCylinder {d : ℕ} (K : Set (Fin (d + 1) → ℝ))
    (p : Fin d → ℝ) (hp : embedSpatial p ∈ K) (h r : ℝ) (hh : 0 < h) (hhr : h < r)
    (m : ℕ) (hm : 0 < m) : bottomSeed h p ∈ nearCylinder K h r (Fin.last d) m := by
  refine ⟨⟨embedSpatial p,hp,(bottomSeed_dist_center h hh p).trans_lt hhr⟩,?_,?_⟩
  · simp [bottomSeed]
  · simpa only [bottomSeed,Fin.snoc_last] using (Int.natCast_pos.mpr hm)

lemma bottomSeed_neighbor_not_mem {d : ℕ} (K : Set (Fin (d + 1) → ℝ))
    (p : Fin d → ℝ) (h r : ℝ) (m : ℕ) :
    (bottomSeed h p).neighbor (Fin.last (d + 1)) ∉ nearCylinder K h r (Fin.last d) m := by
  intro hb
  have hn : ((bottomSeed h p).neighbor (Fin.last (d + 1))).base (Fin.last d) = -1 := by
    simp only [Flag.neighbor, Fin.val_last, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, dite_eq_left, bottomSeed, Flag.cross, Equiv.refl_apply,
      Bool.false_eq_true, ↓reduceIte]
    change Function.update _ (Fin.last d) _ (Fin.last d) = -1
    simp only [Function.update_self]
    have hi : (⟨d + 1 - 1, by omega⟩ : Fin (d + 1)) = Fin.last d := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hi, Fin.snoc_last, zero_add]
  have hneg := hb.2.1
  rw [hn] at hneg
  exact (by norm_num : ¬ (0 : ℤ) ≤ -1) hneg

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- The exact continuation principle needed below, first for an affine initial
model in disjoint neighborhoods of its one free zero orbit. The proof uses
finite equivariant PL perturbation and mod-two boundary pairing. -/
theorem exists_terminal_zero_affine_oai {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    {V : Type u142} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (f : (Fin (d + 1) → ℝ) → V)
    (hf : ContinuousOn f {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1})
    (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hmodel : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      f x = affineOrbitModel H ρ L (embedSpatial p) R p x)
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  by_contra hterm
  let K := {x : Fin (d + 1) → ℝ | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0}
  have hp0 : (embedSpatial p) (Fin.last d) = 0 := by
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0
    simp only [Fin.snoc_last]
  have fp0 : f (embedSpatial p) = 0 := by
    rw [hmodel _ hp0 ⟨1,by simpa using hR⟩]
    have hl : ballLabel (G := H) (embedSpatial p) R (embedSpatial p) = 1 :=
      ballLabel_eq _ _ hR hsep (by simpa using hR)
    simp only [affineOrbitModel,hl,inv_one,one_smul,spatial_embed,sub_self,map_zero]
  have hpK : embedSpatial p ∈ K := ⟨by rw [hp0]; exact ⟨le_refl _,zero_le_one⟩,fp0⟩
  have hKfree : K ⊆ freeLocus (G := H) := fun x hx ↦ hfree x hx.1 hx.2
  obtain ⟨r₀,hr₀,hrt⟩ := compact_free_tube (G := H) hK hKfree
  let r := r₀ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let C := Metric.cthickening r₀ K ∩ {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1}
  have hC : IsCompact C := hK.cthickening.inter_right
    (isClosed_Icc.preimage (continuous_apply (Fin.last d)))
  let U := Metric.thickening (r/2) K ∩ {x | x (Fin.last d) < 1} ∩
    ({x | x (Fin.last d) ≠ 0} ∪ orbitBall (G := H) (embedSpatial p) (R/2))
  have hU : IsOpen U := (Metric.isOpen_thickening.inter
    (isOpen_lt (continuous_apply _) continuous_const)).inter
      ((isOpen_ne_fun (continuous_apply _) continuous_const).union (isOpen_orbitBall _ _))
  have hCU : ∀ x ∈ C, f x = 0 → x ∈ U := by
    intro x hx hfx
    have hxK : x ∈ K := ⟨hx.2,hfx⟩
    refine ⟨⟨Metric.mem_thickening_iff.mpr ⟨x,hxK,by simp; positivity⟩,?_⟩,?_⟩
    · exact lt_of_le_of_ne hx.2.2 (fun he ↦ hterm ⟨x,he,hfx⟩)
    · by_cases ht : x (Fin.last d) = 0
      · obtain ⟨s,rfl⟩ := hz0 x ht hfx
        exact Or.inr ⟨s,by simp; positivity⟩
      · exact Or.inl ht
  obtain ⟨ε,hε,hsmall⟩ := small_norm_near_zeros hC hU f (hf.mono Set.inter_subset_right) hCU
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous (hf.mono Set.inter_subset_right)) (ε/4) (by positivity)
  have hLc : ContinuousAt (fun x : Fin (d + 1) → ℝ ↦ L (spatial x)) (embedSpatial p) :=
    (L.toContinuousLinearEquiv.continuous.comp spatial.continuous_of_finiteDimensional).continuousAt
  obtain ⟨δL,hδL,hδLf⟩ := Metric.continuousAt_iff.mp hLc (ε/8) (by positivity)
  obtain ⟨m,h,hm,hh,hbound,hhm⟩ := exists_positive_mesh
    (min (r/4) (min (R/4) (min δ (δL/4)))) (by positivity)
  have hhr : h < r/4 := (lt_min_iff.mp hbound).1
  have hhR : h < R/4 := (lt_min_iff.mp (lt_min_iff.mp hbound).2).1
  have hhδ : h < δ := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hbound).2).2).1
  have hhδL : h < δL/4 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hbound).2).2).2
  have hsize : r + h/2 ≤ r₀ := by dsimp [r] at *; linarith
  have hKs : ∀ s : H, ∀ x ∈ K, s • x ∈ K := by
    intro s x hx
    constructor
    · change (if s.val.val (Fin.last d) then -x (Fin.last d) else x (Fin.last d)) ∈ _
      simpa only [hHt s,Bool.false_eq_true,↓reduceIte] using hx.1
    · rw [hfe,hx.2,map_zero]
  let D : SubMulAction H (Flag (d + 1)) :=
    ⟨nearCylinder K h r (Fin.last d) m,
      fun s _ hF ↦ nearCylinder_smul K h r (Fin.last d) m s.val (hHt s) (hKs s) hF⟩
  let : Fintype D := (finite_nearCylinder hK.isBounded h r hh (Fin.last d) m).fintype
  have hpoint : ∀ F : D, ∀ k, gridPoint h (F.val.vertex k) ∈ C := by
    intro F k
    rw [gridPoint_vertex]
    exact ⟨Metric.cthickening_mono hsize K
      (nearCylinder_point_cthickening K h r hh.le (Fin.last d) m F.prop k),
      nearCylinder_point_time K h r hh.le (Fin.last d) m hhm F.prop k⟩
  have hvfree : ∀ z : vertices H D, ∀ s : H, s • gridPoint h z.val = gridPoint h z.val → s = 1 := by
    intro z s hs
    obtain ⟨F,k,hFk⟩ := z.prop
    have hmem : gridPoint h z.val ∈ Metric.cthickening r₀ K := by
      rw [← hFk]
      exact (hpoint F k).1
    exact hrt hmem s hs
  let : IsCancelSMul H (vertices H D) := verticesIsCancel H D h hvfree
  obtain ⟨q,w₀,a,hw₀,hwp,hs₀,hj₀,he₀,ha,hap,haf,haug,hvec⟩ :=
    generic_initial_approximation H D ρ L hρ p R h (ε/8) hR hh (by linarith) (by positivity)
      hsep (fun q hqp ↦ by
        have hdq : dist (embedSpatial q) (embedSpatial p) < δL := by linarith
        simpa only [spatial_embed] using hδLf hdq) f hfe hmodel
  let F₀ : D := ⟨bottomSeed h p, bottomSeed_mem_nearCylinder K p hpK h r hh (by linarith) m hm⟩
  apply mesh_parity_contradiction H hHt D ρ L p q R h hR hh (by linarith) hsep
    a ha haug hvec hvfree (fun F k ht hb ↦ haf (flagVertex H D F k) ht hb)
    F₀ rfl (bottomSeed_neighbor_not_mem K p h r m) w₀ hw₀ hwp hs₀ hj₀ he₀
  intro F j hout w hw hs hj hz
  have hxC : F.val.combination h w ∈ C :=
    ⟨Metric.cthickening_mono hsize K
      (nearCylinder_combination_cthickening K h r hh.le (Fin.last d) m F.prop w hw hs),
      nearCylinder_combination_time K h r hh.le (Fin.last d) m hhm F.prop w hw hs⟩
  have hn := norm_at_mesh_zero H D a f h (ε/4) (ε/4) hh.le C
    (fun z ↦ by have hz := hap z; linarith)
    (fun x hx y hy hxy ↦ (hδf x hx y hy (hxy.trans_lt hhδ)).le)
    F w hw hs hz hxC (hpoint F)
  have hxU := hsmall _ hxC (by linarith : ‖f (F.val.combination h w)‖ < ε)
  obtain ⟨hjl,ht,hbase,hcorner⟩ := mesh_boundary_bottom K h r hh (by linarith) m hhm
    F.val F.prop j hout w hw hs hj hxU.1.1 hxU.1.2
  refine ⟨hjl,ht,hbase,hcorner,?_⟩
  have htime : F.val.combination h w (Fin.last d) = 0 := by
    rw [F.val.combination_time_boundary h (Fin.last d) (by simpa using ht) w hs (hjl ▸ hj)]
    simp only [hbase,hcorner,Int.cast_zero,Bool.false_eq_true,↓reduceIte,add_zero,mul_zero]
  exact hxU.2.resolve_left (fun hne ↦ hne htime)

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

theorem solution.{u142} : type_of% @OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine_oai.{u142} := @OAI.SharpLiebThirring.CubeFlags.exists_terminal_zero_affine_oai.{u142}
