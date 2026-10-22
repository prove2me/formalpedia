-- Prove2me | solution 1 for LLLFactor.Reduction.gram_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:26:29.512096+00:00
-- url     : https://prove2.me/submissions/31fed3f8-fc78-4fa1-832b-ce3e58c6f260

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm



namespace LLLFactor.Reduction
open LLLFactor.RedBasis

section Lattice
variable {n : ℕ}

lemma gram_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (v w : ι → Vec n)
    (hw : ∀ a, w a = ∑ b, U a b • v b) :
    Matrix.gram ℝ w = U * Matrix.gram ℝ v * U.transpose := by
  ext a c
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hw a, hw c, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma gram_lin_det {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (v w : ι → Vec n)
    (hw : ∀ a, w a = ∑ b, U a b • v b) :
    (Matrix.gram ℝ w).det = U.det ^ 2 * (Matrix.gram ℝ v).det := by
  rw [gram_lin U v w hw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- `w` generates the same lattice as `v` and has the same Gram determinant. -/
def Good {m : ℕ} (v w : Fin m → Vec n) : Prop :=
  Submodule.span ℤ (Set.range w) = Submodule.span ℤ (Set.range v) ∧
    (Matrix.gram ℝ w).det = (Matrix.gram ℝ v).det

lemma Good.trans {m : ℕ} {u v w : Fin m → Vec n} (h1 : Good u v) (h2 : Good v w) : Good u w :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

lemma good_transv {m : ℕ} (v : Fin m → Vec n) (j l : Fin m) (hjl : j ≠ l) (s : ℤ) :
    Good v (Function.update v l (v l + s • v j)) := by
  set w := Function.update v l (v l + s • v j) with hw
  have hwl : w l = v l + s • v j := by simp [hw]
  have hwj : w j = v j := by simp [hw, Function.update_of_ne hjl]
  have hwa : ∀ a, a ≠ l → w a = v a := fun a ha => by simp [hw, Function.update_of_ne ha]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · apply Submodule.span_le.2
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = l
    · subst ha
      rw [hwl]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨a, rfl⟩)
        (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    · rw [hwa a ha]; exact Submodule.subset_span ⟨a, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = l
    · subst ha
      have : v a = w a - s • w j := by rw [hwl, hwj]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩)
        (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    · rw [← hwa a ha]; exact Submodule.subset_span ⟨a, rfl⟩
  · have := gram_lin_det (Matrix.transvection l j (s : ℝ)) v w ?_
    · rw [this, Matrix.det_transvection_of_ne l j hjl.symm, one_pow, one_mul]
    · intro a
      by_cases ha : a = l
      · subst ha
        simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, add_smul,
          Finset.sum_add_distrib, Matrix.single_apply, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, true_and, hwl]
        rw [Int.cast_smul_eq_zsmul]
      · have hla : l ≠ a := fun h => ha h.symm
        simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, add_smul,
          Finset.sum_add_distrib, Matrix.single_apply, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true, hla, false_and,
          if_false, Finset.sum_const_zero, add_zero]
        rw [hwa a ha]

lemma good_neg {m : ℕ} (v : Fin m → Vec n) (j : Fin m) :
    Good v (Function.update v j (-v j)) := by
  set w := Function.update v j (-v j) with hw
  have hwj : w j = -v j := by simp [hw]
  have hwa : ∀ a, a ≠ j → w a = v a := fun a ha => by simp [hw, Function.update_of_ne ha]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · apply Submodule.span_le.2
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = j
    · subst ha
      rw [hwj]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [hwa a ha]; exact Submodule.subset_span ⟨a, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨a, rfl⟩
    by_cases ha : a = j
    · subst ha
      have : v a = -w a := by rw [hwj, neg_neg]
      rw [this]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [← hwa a ha]; exact Submodule.subset_span ⟨a, rfl⟩
  · have := gram_lin_det (Matrix.diagonal fun a => if a = j then (-1 : ℝ) else 1) v w ?_
    · rw [this, Matrix.det_diagonal]
      have : ∏ a : Fin m, (if a = j then (-1 : ℝ) else 1) = -1 := by
        rw [Finset.prod_ite_eq']; simp
      rw [this]; norm_num
    · intro a
      by_cases ha : a = j
      · subst ha
        simp [Matrix.diagonal_apply, hwj]
      · simp [Matrix.diagonal_apply, ha, hwa a ha]

lemma good_swap {m : ℕ} (v : Fin m → Vec n) (p q : Fin m) :
    Good v (v ∘ Equiv.swap p q) := by
  refine ⟨by rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ], ?_⟩
  have : Matrix.gram ℝ (v ∘ Equiv.swap p q) = (Matrix.gram ℝ v).submatrix (Equiv.swap p q) (Equiv.swap p q) := rfl
  rw [this, Matrix.det_submatrix_equiv_self]


lemma euclid_step {m : ℕ} (v : Fin m → Vec n) (a : Fin m → ℤ) (j l : Fin m) (hjl : j ≠ l)
    (hl : a l ≠ 0) (hle : |a l| ≤ |a j|) :
    ∃ (v' : Fin m → Vec n) (a' : Fin m → ℤ), Good v v' ∧
      ∑ c, a' c • v' c = ∑ c, a c • v c ∧ ∑ c, |a' c| < ∑ c, |a c| := by
  have hj : a j ≠ 0 := by
    intro h; rw [h, abs_zero] at hle
    exact hl (abs_nonpos_iff.1 hle)
  set s : ℤ := Int.sign (a j) * Int.sign (a l) with hs
  have habs : |a j - s * a l| = |a j| - |a l| := by
    rw [hs]
    rcases lt_or_gt_of_ne hj with h1 | h1 <;> rcases lt_or_gt_of_ne hl with h2 | h2
    · rw [Int.sign_eq_neg_one_of_neg h1, Int.sign_eq_neg_one_of_neg h2]
      rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg] at *; omega
    · rw [Int.sign_eq_neg_one_of_neg h1, Int.sign_eq_one_of_pos h2]
      rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg] at *; omega
    · rw [Int.sign_eq_one_of_pos h1, Int.sign_eq_neg_one_of_neg h2]
      rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg] at *; omega
    · rw [Int.sign_eq_one_of_pos h1, Int.sign_eq_one_of_pos h2]
      rw [abs_eq_max_neg, abs_eq_max_neg, abs_eq_max_neg] at *; omega
  refine ⟨Function.update v l (v l + s • v j), Function.update a j (a j - s * a l),
    good_transv v j l hjl s, ?_, ?_⟩
  · have hpt : ∀ c, Function.update a j (a j - s * a l) c • Function.update v l (v l + s • v j) c =
        a c • v c + (if c = j then (-(s * a l)) • v j else 0) +
          (if c = l then (s * a l) • v j else 0) := by
      intro c
      by_cases hcj : c = j
      · subst hcj
        have : c ≠ l := hjl
        simp [Function.update_of_ne this, this, sub_smul, mul_smul]
        try abel
      · by_cases hcl : c = l
        · subst hcl
          simp [Function.update_of_ne hcj, hcj, smul_add, mul_smul, mul_comm]
          try abel
        · simp [Function.update_of_ne hcj, Function.update_of_ne hcl, hcj, hcl]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [add_assoc]
    have : (-(s * a l)) • v j + (s * a l) • v j = 0 := by rw [← add_smul]; simp
    rw [this, add_zero]
  · have e1 := Finset.add_sum_erase Finset.univ (fun c => |Function.update a j (a j - s * a l) c|)
      (Finset.mem_univ j)
    have e2 := Finset.add_sum_erase Finset.univ (fun c => |a c|) (Finset.mem_univ j)
    have e3 : ∑ c ∈ Finset.univ.erase j, |Function.update a j (a j - s * a l) c| =
        ∑ c ∈ Finset.univ.erase j, |a c| :=
      Finset.sum_congr rfl fun c hc => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
    simp only [Function.update_self] at e1
    rw [← e1, ← e2, e3, habs]
    have : 0 < |a l| := abs_pos.2 hl
    omega


lemma euclid_base (i : ℕ) (v : Fin (i + 1) → Vec n) (a : Fin (i + 1) → ℤ)
    (hx : ∑ c, a c • v c ≠ 0)
    (hprim : ∀ y ∈ Submodule.span ℤ (Set.range v), ∀ k : ℤ, ∑ c, a c • v c = k • y →
      k = 1 ∨ k = -1)
    (hnp : ∀ j l, j ≠ l → a j ≠ 0 → a l = 0) :
    ∃ w, Good v w ∧ w 0 = ∑ c, a c • v c := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    exact Finset.sum_eq_zero fun c _ => by rw [h c, zero_smul]
  have hxj : ∑ c, a c • v c = a j • v j := by
    rw [Finset.sum_eq_single j]
    intro c _ hc
    rw [hnp j c hc.symm hj, zero_smul]
    intro h; exact absurd (Finset.mem_univ j) h
  rw [hxj] at hprim ⊢
  rcases hprim (v j) (Submodule.subset_span ⟨j, rfl⟩) (a j) rfl with h | h
  · refine ⟨v ∘ Equiv.swap 0 j, good_swap v 0 j, ?_⟩
    simp [h]
  · refine ⟨(Function.update v j (-v j)) ∘ Equiv.swap 0 j,
      (good_neg v j).trans (good_swap _ 0 j), ?_⟩
    simp [h]

lemma euclid (i : ℕ) : ∀ (N : ℕ) (v : Fin (i + 1) → Vec n) (a : Fin (i + 1) → ℤ),
    (∑ c, |a c|) ≤ (N : ℤ) → ∑ c, a c • v c ≠ 0 →
    (∀ y ∈ Submodule.span ℤ (Set.range v), ∀ k : ℤ, ∑ c, a c • v c = k • y → k = 1 ∨ k = -1) →
    ∃ w, Good v w ∧ w 0 = ∑ c, a c • v c := by
  intro N
  induction N with
  | zero =>
    intro v a hN hx _
    exfalso; apply hx
    have h0 : ∀ c, a c = 0 := by
      intro c
      have h1 : |a c| ≤ ∑ c, |a c| :=
        Finset.single_le_sum (f := fun c => |a c|) (fun c _ => abs_nonneg _) (Finset.mem_univ c)
      have : |a c| ≤ 0 := by simpa using h1.trans hN
      exact abs_nonpos_iff.1 this
    exact Finset.sum_eq_zero fun c _ => by rw [h0 c, zero_smul]
  | succ N ih =>
    intro v a hN hx hprim
    by_cases hpair : ∃ j l, j ≠ l ∧ a j ≠ 0 ∧ a l ≠ 0
    · obtain ⟨j, l, hjl, hj, hl⟩ := hpair
      have key : ∃ (v' : Fin (i + 1) → Vec n) (a' : Fin (i + 1) → ℤ), Good v v' ∧
          ∑ c, a' c • v' c = ∑ c, a c • v c ∧ ∑ c, |a' c| < ∑ c, |a c| := by
        rcases le_total |a l| |a j| with h | h
        · exact euclid_step v a j l hjl hl h
        · exact euclid_step v a l j hjl.symm hj h
      obtain ⟨v', a', hg, hsum, hlt⟩ := key
      have := ih v' a' (by push_cast at hN; omega) (by rw [hsum]; exact hx) (by
        intro y hy k hk
        rw [hg.1] at hy
        rw [hsum] at hk
        exact hprim y hy k hk)
      obtain ⟨w, hw1, hw2⟩ := this
      exact ⟨w, hg.trans hw1, by rw [hw2, hsum]⟩
    · push Not at hpair
      exact euclid_base i v a hx hprim hpair


lemma exists_min_vec {m : ℕ} (v : Fin m → Vec n) (hv : LinearIndependent ℝ v) (hm : 0 < m) :
    ∃ x ∈ Submodule.span ℤ (Set.range v), x ≠ 0 ∧
      ∀ y ∈ Submodule.span ℤ (Set.range v), y ≠ 0 → ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have hs : LinearIndepOn ℝ id (Set.range v) := hv.linearIndepOn_id
  let B := Module.Basis.extend hs
  haveI : Finite (hs.extend (Set.subset_univ _)) := Module.Finite.finite_basis B
  have hrange : Set.range v ⊆ Set.range B := by
    rw [Module.Basis.range_extend]
    exact hs.subset_extend _
  have hM : Submodule.span ℤ (Set.range v) ≤ Submodule.span ℤ (Set.range B) :=
    Submodule.span_mono hrange
  set x0 : Vec n := v ⟨0, hm⟩ with hx0
  have hx0ne : x0 ≠ 0 := hv.ne_zero _
  have hx0M : x0 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨_, rfl⟩
  have hfin : Set.Finite (Metric.closedBall (0 : Vec n) ‖x0‖ ∩ Submodule.span ℤ (Set.range B)) :=
    ZSpan.setFinite_inter B Metric.isBounded_closedBall
  set T : Set (Vec n) := {y | y ∈ Submodule.span ℤ (Set.range v) ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖} with hT
  have hTfin : T.Finite := by
    refine hfin.subset ?_
    rintro y ⟨hy1, _, hy3⟩
    exact ⟨by simpa using hy3, hM hy1⟩
  obtain ⟨x, hxT, hxmin⟩ := Set.exists_min_image T (fun y => ‖y‖) hTfin ⟨x0, hx0M, hx0ne, le_rfl⟩
  refine ⟨x, hxT.1, hxT.2.1, fun y hy hy0 => ?_⟩
  by_cases hyR : ‖y‖ ≤ ‖x0‖
  · have := hxmin y ⟨hy, hy0, hyR⟩
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  · have h1 : ‖x‖ ≤ ‖x0‖ := hxT.2.2
    have : ‖x‖ ≤ ‖y‖ := h1.trans (le_of_not_ge hyR)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2


lemma shortest_prim {m : ℕ} (v : Fin m → Vec n) (x : Vec n) (hx0 : x ≠ 0)
    (hmin : ∀ y ∈ Submodule.span ℤ (Set.range v), y ≠ 0 → ‖x‖ ^ 2 ≤ ‖y‖ ^ 2) :
    ∀ y ∈ Submodule.span ℤ (Set.range v), ∀ k : ℤ, x = k • y → k = 1 ∨ k = -1 := by
  intro y hy k hk
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [smul_zero] at hk; exact hx0 hk
  have h := hmin y hy hy0
  have hn : ‖x‖ = |(k : ℝ)| * ‖y‖ := by
    rw [hk, ← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have h2 : ((k : ℝ)) ^ 2 ≤ 1 := by
    rw [hn, mul_pow, sq_abs] at h
    have : (k : ℝ) ^ 2 * ‖y‖ ^ 2 ≤ 1 * ‖y‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_right this (by positivity)
  have h3 : k ^ 2 ≤ 1 := by exact_mod_cast h2
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [zero_smul] at hk; exact hx0 hk
  have : -1 ≤ k ∧ k ≤ 1 := by constructor <;> nlinarith
  omega

noncomputable def projTail {i : ℕ} (w : Fin (i + 1) → Vec n) : Fin i → Vec n :=
  fun j => w j.succ - (inner ℝ (w j.succ) (w 0) / ‖w 0‖ ^ 2) • w 0

lemma proj_gram (i : ℕ) (w : Fin (i + 1) → Vec n) (hx : w 0 ≠ 0) :
    (Matrix.gram ℝ w).det = ‖w 0‖ ^ 2 * (Matrix.gram ℝ (projTail w)).det := by
  set t : Fin (i + 1) → ℝ := fun a => if a = 0 then 0 else inner ℝ (w a) (w 0) / ‖w 0‖ ^ 2 with ht
  set u : Fin (i + 1) → Vec n := fun a => w a - t a • w 0 with hu
  have hu0 : u 0 = w 0 := by simp [hu, ht]
  have husucc : ∀ j : Fin i, u j.succ = projTail w j := by
    intro j; simp [hu, ht, projTail, Fin.succ_ne_zero]
  set U : Matrix (Fin (i + 1)) (Fin (i + 1)) ℝ :=
    Matrix.of fun a b => (if a = b then 1 else 0) - (if b = 0 then t a else 0) with hU
  have hUw : ∀ a, u a = ∑ b, U a b • w b := by
    intro a
    simp only [hU, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hu]
    simp [sub_eq_add_neg]
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · apply Finset.prod_eq_one
      intro a _
      simp only [hU, Matrix.of_apply, if_true]
      by_cases ha : a = 0
      · subst ha; simp [ht]
      · simp [ha]
    · intro a b hab
      have hab' : a < b := hab
      have hb0 : b ≠ 0 := by
        intro h; subst h; exact absurd hab' (not_lt.2 (Fin.zero_le _))
      simp [hU, hab'.ne, hb0]
  have h1 : (Matrix.gram ℝ u).det = (Matrix.gram ℝ w).det := by
    rw [gram_lin_det U w u hUw, hUdet]; ring
  have hnorm : ‖w 0‖ ^ 2 ≠ 0 := by positivity
  have hortho : ∀ j : Fin i, inner ℝ (w 0) (u j.succ) = 0 := by
    intro j
    rw [husucc, projTail, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm]
    field_simp
    ring
  have h2 : (Matrix.gram ℝ u).det = ‖w 0‖ ^ 2 * (Matrix.gram ℝ (projTail w)).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.gram_apply, Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul, hu0,
      real_inner_self_eq_norm_sq]
    have hs : ∑ x : Fin i, (-1 : ℝ) ^ (x.succ : ℕ) * inner ℝ (w 0) (u x.succ) *
        ((Matrix.gram ℝ u).submatrix Fin.succ x.succ.succAbove).det = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hortho j]; simp
    have hm : (Matrix.gram ℝ u).submatrix Fin.succ Fin.succ = Matrix.gram ℝ (projTail w) := by
      ext a b; simp [Matrix.gram_apply, husucc]
    rw [hs, add_zero, hm]
  rw [← h1, h2]


lemma proj_min (i : ℕ) (w : Fin (i + 1) → Vec n) (M : Submodule ℤ (Vec n))
    (hw : ∀ a, w a ∈ M) (hx : w 0 ≠ 0)
    (hmin : ∀ y ∈ M, y ≠ 0 → ‖w 0‖ ^ 2 ≤ ‖y‖ ^ 2) :
    ∀ z ∈ Submodule.span ℤ (Set.range (projTail w)), z ≠ 0 →
      (3 / 4 : ℝ) * ‖w 0‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  intro z hz hz0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hz
  have hxpos : 0 < ‖w 0‖ ^ 2 := by positivity
  set z := ∑ j, c j • projTail w j with hzdef
  have hzr : z = ∑ j, (c j : ℝ) • projTail w j := by
    simp only [hzdef, Int.cast_smul_eq_zsmul]
  have hproj : ∀ j, inner ℝ (projTail w j) (w 0) = 0 := by
    intro j
    simp only [projTail, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hzx : inner ℝ z (w 0) = 0 := by
    rw [hzr, sum_inner]
    exact Finset.sum_eq_zero fun j _ => by rw [real_inner_smul_left, hproj j, mul_zero]
  set y : Vec n := ∑ j, c j • w j.succ with hydef
  set τ : ℝ := ∑ j, (c j : ℝ) * (inner ℝ (w j.succ) (w 0) / ‖w 0‖ ^ 2) with hτ
  have hy : y ∈ M := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw _)
  have hzy : z = y - τ • w 0 := by
    rw [hzr, hydef, hτ, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [projTail, smul_sub, Int.cast_smul_eq_zsmul, mul_smul]
  set k : ℤ := round τ with hk
  have hyk : y - k • w 0 ∈ M := Submodule.sub_mem _ hy (Submodule.smul_mem _ _ (hw 0))
  have hy' : y - k • w 0 = z + (τ - k) • w 0 := by
    rw [hzy, ← Int.cast_smul_eq_zsmul ℝ, sub_smul]; abel
  have hnorm : ‖y - k • w 0‖ ^ 2 = ‖z‖ ^ 2 + (τ - k) ^ 2 * ‖w 0‖ ^ 2 := by
    rw [hy', norm_add_sq_real, real_inner_smul_right, hzx, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  have hne : y - k • w 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    nlinarith [sq_nonneg (τ - k), mul_nonneg (sq_nonneg (τ - k)) hxpos.le]
  have h1 := hmin _ hyk hne
  have h2 : |τ - k| ≤ 1 / 2 := abs_sub_round τ
  have h3 : (τ - k) ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (by linarith [abs_le.1 h2]) (abs_le.1 h2).2
    nlinarith [abs_le.1 h2]
  rw [hnorm] at h1
  nlinarith [mul_le_mul_of_nonneg_right h3 hxpos.le]


lemma tri_succ (i : ℕ) : (i + 1) * (i + 1 - 1) / 2 = i * (i - 1) / 2 + i := by
  rcases i with _ | j
  · simp
  · have : (j + 1 + 1) * (j + 1 + 1 - 1) = (j + 1) * (j + 1 - 1) + 2 * (j + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

theorem hermite_aux : ∀ (i : ℕ) (v : Fin i → Vec n), LinearIndependent ℝ v → ∀ μ : ℝ, 0 ≤ μ →
    (∀ y ∈ Submodule.span ℤ (Set.range v), y ≠ 0 → μ ≤ ‖y‖ ^ 2) →
    (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * μ ^ i ≤ (Matrix.gram ℝ v).det := by
  intro i
  induction i with
  | zero =>
    intro v _ μ _ _
    simp
  | succ i ih =>
    intro v hv μ hμ hlow
    obtain ⟨x, hxM, hx0, hxmin⟩ := exists_min_vec v hv (Nat.succ_pos i)
    have hmu : μ ≤ ‖x‖ ^ 2 := hlow x hxM hx0
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxM
    obtain ⟨w, hgood, hw0⟩ := euclid i (∑ c, |a c|).toNat v a
      (by rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun c _ => abs_nonneg _)])
      (by rw [ha]; exact hx0)
      (by rw [ha]; exact shortest_prim v x hx0 hxmin)
    rw [ha] at hw0
    have hdetv : (Matrix.gram ℝ v).det ≠ 0 := Matrix.det_gram_ne_zero_iff_linearIndependent.2 hv
    have hdetw : (Matrix.gram ℝ w).det = (Matrix.gram ℝ v).det := hgood.2
    have hxw : w 0 ≠ 0 := by rw [hw0]; exact hx0
    have hpg := proj_gram i w hxw
    have hm'pos : 0 < ‖w 0‖ ^ 2 := by positivity
    have hdet' : (Matrix.gram ℝ (projTail w)).det ≠ 0 := by
      intro h; rw [h, mul_zero] at hpg; exact hdetv (hdetw ▸ hpg)
    have hind : LinearIndependent ℝ (projTail w) :=
      Matrix.linearIndependent_of_det_gram_ne_zero hdet'
    have hwM : ∀ c, w c ∈ Submodule.span ℤ (Set.range v) := by
      intro c; rw [← hgood.1]; exact Submodule.subset_span ⟨c, rfl⟩
    have hmin' : ∀ y ∈ Submodule.span ℤ (Set.range v), y ≠ 0 → ‖w 0‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hw0]; exact hxmin
    have hlow' := proj_min i w _ hwM hxw hmin'
    have key := ih (projTail w) hind ((3 / 4) * ‖w 0‖ ^ 2) (by positivity) hlow'
    have hmw : μ ≤ ‖w 0‖ ^ 2 := by rw [hw0]; exact hmu
    calc (3 / 4 : ℝ) ^ ((i + 1) * (i + 1 - 1) / 2) * μ ^ (i + 1)
        = (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * (3 / 4 : ℝ) ^ i * μ ^ (i + 1) := by
          rw [tri_succ, pow_add]
      _ ≤ (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * (3 / 4 : ℝ) ^ i * (‖w 0‖ ^ 2) ^ (i + 1) := by
          gcongr
      _ = ‖w 0‖ ^ 2 * ((3 / 4 : ℝ) ^ (i * (i - 1) / 2) * ((3 / 4) * ‖w 0‖ ^ 2) ^ i) := by
          rw [mul_pow, pow_succ]; ring
      _ ≤ ‖w 0‖ ^ 2 * (Matrix.gram ℝ (projTail w)).det := by gcongr
      _ = (Matrix.gram ℝ v).det := by rw [← hpg, hdetw]


theorem gram_lower_core (hn : 0 < n) (c : Fin n → Vec n) (L : Submodule ℤ (Vec n))
    (hc : IsBasisFor c L) :
    0 < minSqNorm L ∧
    (∃ x ∈ L, x ≠ 0 ∧ ‖x‖ ^ 2 = minSqNorm L) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * minSqNorm L ^ i ≤ gram c i := by
  obtain ⟨hind, hL⟩ := hc
  have hL' : Submodule.span ℤ (Set.range c) = L := hL
  obtain ⟨x, hxM, hx0, hxmin⟩ := exists_min_vec c hind hn
  rw [hL'] at hxM
  have hS : minSqNorm L = ‖x‖ ^ 2 := by
    unfold minSqNorm
    apply IsLeast.csInf_eq
    refine ⟨⟨x, hxM, hx0, rfl⟩, ?_⟩
    rintro r ⟨y, hy, hy0, rfl⟩
    exact hxmin y (by rw [hL']; exact hy) hy0
  have hpos : 0 < minSqNorm L := by rw [hS]; positivity
  refine ⟨hpos, ⟨x, hxM, hx0, hS.symm⟩, ?_⟩
  intro i _ hi
  have hv : LinearIndependent ℝ (fun a : Fin i => c (Fin.castLE hi a)) :=
    hind.comp _ (Fin.castLE_injective hi)
  have hlow : ∀ y ∈ Submodule.span ℤ (Set.range (fun a : Fin i => c (Fin.castLE hi a))),
      y ≠ 0 → minSqNorm L ≤ ‖y‖ ^ 2 := by
    intro y hy hy0
    have hyL : y ∈ L := by
      rw [← hL']
      refine Submodule.span_mono ?_ hy
      rintro _ ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    unfold minSqNorm
    exact csInf_le ⟨0, by rintro r ⟨z, _, _, rfl⟩; positivity⟩ ⟨y, hyL, hy0, rfl⟩
  have := hermite_aux i _ hv (minSqNorm L) hpos.le hlow
  unfold gram
  rw [dif_pos hi]
  exact this

end Lattice
end LLLFactor.Reduction

open LLLFactor.Reduction


theorem solution {n : ℕ} (hn : 0 < n) (c : Fin n → LLLFactor.RedBasis.Vec n)
    (L : Submodule ℤ (LLLFactor.RedBasis.Vec n)) (hc : LLLFactor.RedBasis.IsBasisFor c L) :
    0 < minSqNorm L ∧
    (∃ x ∈ L, x ≠ 0 ∧ ‖x‖ ^ 2 = minSqNorm L) ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      (3 / 4 : ℝ) ^ (i * (i - 1) / 2) * minSqNorm L ^ i ≤ gram c i := by
  exact gram_lower_core hn c L hc
