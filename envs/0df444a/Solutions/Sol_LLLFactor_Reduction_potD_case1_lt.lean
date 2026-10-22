-- Prove2me | solution 1 for LLLFactor.Reduction.potD_case1_lt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:16:30.733252+00:00
-- url     : https://prove2.me/submissions/cd7444a7-0031-4f7d-b15d-4368ea06eae2

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm



namespace LLLFactor.Reduction
open LLLFactor.RedBasis

section GS
variable {n : ℕ}

lemma gs_orth (b : Fin n → Vec n) {i j : Fin n} (h : i ≠ j) :
    inner ℝ (gs b i) (gs b j) = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal ℝ b h

lemma mu_eq (b : Fin n → Vec n) (i j : Fin n) :
    mu b i j = inner ℝ (gs b j) (b i) / inner ℝ (gs b j) (gs b j) := by
  unfold mu; rw [real_inner_comm]

lemma b_eq (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
  have h := InnerProductSpace.gramSchmidt_def'' ℝ b i
  conv_lhs => rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mu_eq]
  simp only [gs, real_inner_self_eq_norm_sq]
  simp

lemma proj_id (b : Fin n → Vec n) (i : Fin n) (δ : Vec n)
    (hδ : δ ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∑ j ∈ Finset.Iio i, (inner ℝ (gs b j) δ / inner ℝ (gs b j) (gs b j)) • gs b j = δ := by
  induction hδ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : l ∈ Finset.Iio i := by simpa using hl
    rw [Finset.sum_eq_single_of_mem l hl']
    · by_cases h0 : gs b l = 0
      · simp [h0]
      · have : inner ℝ (gs b l) (gs b l) ≠ 0 := by simpa using h0
        rw [div_self this, one_smul]
    · intro j _ hj
      rw [gs_orth b hj, zero_div, zero_smul]
  | zero => simp
  | add x y _ _ ihx ihy =>
    simp only [inner_add_right, add_div, add_smul, Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ihx =>
    simp only [inner_smul_right, mul_div_assoc, mul_smul, ← Finset.smul_sum, ihx]

lemma gs_shift (b b' : Fin n → Vec n) (t : Fin n)
    (h : ∀ i ≤ t, b' i - b i ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∀ i ≤ t, gs b' i = gs b i := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  intro hi
  have key : ∀ j ∈ Finset.Iio i, gs b' j = gs b j := fun j hj =>
    ih j (Finset.mem_Iio.1 hj) ((Finset.mem_Iio.1 hj).le.trans hi)
  have h1 := b_eq b i
  have h2 := b_eq b' i
  have hp := proj_id b i (b' i - b i) (h i hi)
  have hb' : b' i = b i + (b' i - b i) := by abel
  have e1 : b i - gs b i = ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
    rw [sub_eq_iff_eq_add']; exact h1
  have hsum : ∑ j ∈ Finset.Iio i, mu b' i j • gs b' j =
      (b i - gs b i) + (b' i - b i) := by
    rw [← hp, e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mu_eq, mu_eq, key j hj, ← add_smul, ← add_div, ← inner_add_right, add_sub_cancel]
  have : gs b' i = gs b i := by
    have := h2
    rw [hsum] at this
    have h3 : gs b' i = b' i - ((b i - gs b i) + (b' i - b i)) := by
      rw [eq_sub_iff_add_eq]; exact this.symm
    rw [h3]; abel
  exact this


lemma gs_prefix (b b' : Fin n → Vec n) (t : Fin n) (h : ∀ j ≤ t, b' j = b j) :
    ∀ i ≤ t, gs b' i = gs b i :=
  gs_shift b b' t (fun i hi => by rw [h i hi, sub_self]; exact Submodule.zero_mem _)

lemma reduceBy_self (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    reduceBy c κ l r κ = c κ - (r : ℝ) • c l := by
  simp [reduceBy]

lemma reduceBy_ne (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) (j : Fin n) (h : j ≠ κ) :
    reduceBy c κ l r j = c j := by
  simp [reduceBy, Function.update_of_ne h]

lemma gs_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i : Fin n) :
    gs (reduceBy c κ l r) i = gs c i := by
  refine gs_shift c (reduceBy c κ l r) i ?_ i le_rfl
  intro i' _
  by_cases h : i' = κ
  · subst h
    rw [reduceBy_self]
    have h1 : c l ∈ Submodule.span ℝ (gs c '' Set.Iic l) :=
      InnerProductSpace.mem_span_gramSchmidt ℝ c (le_refl l)
    have h2 : c l ∈ Submodule.span ℝ (gs c '' Set.Iio i') :=
      Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.2 hl)) h1
    have : c i' - (r : ℝ) • c l - c i' = -((r : ℝ) • c l) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ h2)
  · rw [reduceBy_ne c κ l r i' h, sub_self]; exact Submodule.zero_mem _

lemma mu_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i j : Fin n) :
    mu (reduceBy c κ l r) i j = if i = κ then mu c κ j - r * mu c l j else mu c i j := by
  rw [mu_eq, gs_reduceBy c κ l hl]
  by_cases h : i = κ
  · subst h
    rw [if_pos rfl, reduceBy_self, mu_eq, mu_eq, inner_sub_right, real_inner_smul_right, sub_div,
      mul_div_assoc]
  · rw [if_neg h, reduceBy_ne c κ l r i h, mu_eq]

lemma mu_self (c : Fin n → Vec n) (l : Fin n) (h : gs c l ≠ 0) : mu c l l = 1 := by
  rw [mu_eq]
  have h1 := b_eq c l
  have h2 : inner ℝ (gs c l) (c l) = inner ℝ (gs c l) (gs c l) := by
    conv_lhs => rw [h1]
    rw [inner_add_right, inner_sum]
    have : ∑ x ∈ Finset.Iio l, inner ℝ (gs c l) (mu c l x • gs c x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [real_inner_smul_right, gs_orth c (Finset.mem_Iio.1 hx).ne', mul_zero]
    rw [this, add_zero]
  rw [h2]
  exact div_self (by simpa using h)

lemma mu_zero_of_lt (c : Fin n → Vec n) {i j : Fin n} (h : i < j) : mu c i j = 0 := by
  have := InnerProductSpace.gramSchmidt_inv_triangular ℝ c h
  rw [mu_eq]; change inner ℝ (InnerProductSpace.gramSchmidt ℝ c j) (c i) = 0 at this
  rw [show inner ℝ (gs c j) (c i) = 0 from this, zero_div]


lemma Sit_mono {b : Fin n → Vec n} {k k' : ℕ} (h : Situation b k) (hk : k' ≤ k) :
    Situation b k' :=
  ⟨fun i j hji hik => h.1 i j hji (by omega), fun i h2 hik hin => h.2 i h2 (by omega) hin⟩

lemma Cond120_congr {b b' : Fin n → Vec n} {i : ℕ} (hbb : ∀ j : Fin n, (j : ℕ) < i → b' j = b j)
    (h : Cond120 b i) : Cond120 b' i := by
  obtain ⟨hi, h0⟩ := h
  refine ⟨hi, ?_⟩
  have hg : ∀ m : Fin n, (m : ℕ) < i → gs b' m = gs b m := fun m hm =>
    gs_prefix b b' m (fun j hj => hbb j (lt_of_le_of_lt hj hm)) m le_rfl
  have e1 := hg ⟨i - 1, by omega⟩ (by simp; omega)
  have e2 := hg ⟨i - 2, by omega⟩ (by simp; omega)
  have e3 : mu b' ⟨i - 1, by omega⟩ ⟨i - 2, by omega⟩ = mu b ⟨i - 1, by omega⟩ ⟨i - 2, by omega⟩ := by
    rw [mu_eq, mu_eq, e2, hbb ⟨i - 1, by omega⟩ (by simp; omega)]
  rw [e1, e2, e3]
  exact h0

lemma Sit_congr {b b' : Fin n → Vec n} {k : ℕ} (hbb : ∀ j : Fin n, (j : ℕ) + 1 < k → b' j = b j)
    (h : Situation b k) : Situation b' k := by
  constructor
  · intro i j hji hik
    have := h.1 i j hji hik
    have e2 : gs b' j = gs b j :=
      gs_prefix b b' j (fun m hm => hbb m (by have : (m:ℕ) ≤ j := hm; have : (j:ℕ) < i := hji; omega))
        j le_rfl
    rw [mu_eq, e2, hbb i hik, ← mu_eq]
    exact this
  · intro i h2 hik hin
    exact Cond120_congr (fun j hj => hbb j (by omega)) (h.2 i h2 hik hin)

lemma achieve118_cases {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') :
    (b' = b ∧ ∀ (hk : 2 ≤ k ∧ k ≤ n),
        |mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2) ∨
    (∃ (hk : 2 ≤ k ∧ k ≤ n) (r : ℤ),
        b' = reduceBy b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ r ∧
        IsNearestInt r (mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩)) := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨h1, h2⟩ | ⟨h1, r, h2, h3⟩
    · left; exact ⟨h2, fun _ => h1⟩
    · right; exact ⟨hk, r, h3, h2⟩
  · left; exact ⟨h, fun hk' => absurd hk' hk⟩

lemma achieve118_ne {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') (j : Fin n)
    (hj : (j : ℕ) ≠ k - 1) : b' j = b j := by
  rcases achieve118_cases h with ⟨h1, _⟩ | ⟨hk, r, h1, _⟩
  · rw [h1]
  · rw [h1, reduceBy_ne]
    intro e; apply hj; rw [e]

lemma achieve118_gs {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') (i : Fin n) :
    gs b' i = gs b i := by
  rcases achieve118_cases h with ⟨h1, _⟩ | ⟨hk, r, h1, _⟩
  · rw [h1]
  · rw [h1]
    exact gs_reduceBy b _ _ (by simp [Fin.lt_def]; omega) r i

lemma achieve118_mu {b b' : Fin n → Vec n} {k : ℕ} (hb : LinearIndependent ℝ b)
    (h : Achieve118 b k b') (hk : 2 ≤ k ∧ k ≤ n) :
    |mu b' ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2 := by
  rcases achieve118_cases h with ⟨h1, h2⟩ | ⟨hk', r, h1, h2⟩
  · rw [h1]; exact h2 hk
  · have hlt : (⟨k - 2, by omega⟩ : Fin n) < ⟨k - 1, by omega⟩ := by simp [Fin.lt_def]; omega
    rw [h1, mu_reduceBy _ _ _ hlt, if_pos rfl,
      mu_self b _ (InnerProductSpace.gramSchmidt_ne_zero _ hb), mul_one]
    exact h2

lemma loopstep_props {κ : Fin n} {c c' : Fin n → Vec n} (h : LoopStep κ c c') :
    (∀ i, gs c' i = gs c i) ∧ (∀ j, j ≠ κ → c' j = c j) ∧
    (∀ p : Fin n, (p : ℕ) + 1 = κ → |mu c κ p| ≤ 1 / 2 → mu c' κ p = mu c κ p) := by
  obtain ⟨l, hl, hbig, _, r, _, rfl⟩ := h
  refine ⟨gs_reduceBy c κ l hl r, fun j hj => reduceBy_ne c κ l r j hj, ?_⟩
  intro p hp hle
  have hlp : l < p := by
    have h1 : (l : ℕ) < κ := hl
    have h2 : l ≠ p := by
      rintro rfl; linarith
    have h3 : (l : ℕ) ≠ p := fun e => h2 (Fin.ext e)
    rw [Fin.lt_def]; omega
  rw [mu_reduceBy c κ l hl, if_pos rfl, mu_zero_of_lt c hlp]
  simp

lemma loop_props {κ : Fin n} {c c' : Fin n → Vec n}
    (h : Relation.ReflTransGen (LoopStep κ) c c') :
    (∀ i, gs c' i = gs c i) ∧ (∀ j, j ≠ κ → c' j = c j) ∧
    (∀ p : Fin n, (p : ℕ) + 1 = κ → |mu c κ p| ≤ 1 / 2 → mu c' κ p = mu c κ p) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨g1, g2, g3⟩ := ih
    obtain ⟨s1, s2, s3⟩ := loopstep_props hs
    refine ⟨fun i => (s1 i).trans (g1 i), fun j hj => (s2 j hj).trans (g2 j hj), ?_⟩
    intro p hp hle
    have := g3 p hp hle
    rw [s3 p hp (by rw [this]; exact hle), this]


end GS

section Gram
variable {n : ℕ}

noncomputable def Umat (b : Fin n → Vec n) (j l : Fin n) : ℝ :=
  (if l < j then mu b j l else 0) + (if l = j then 1 else 0)

lemma b_eq_U (b : Fin n → Vec n) (j : Fin n) : b j = ∑ l : Fin n, Umat b j l • gs b l := by
  have h1 := b_eq b j
  have h2 : ∑ l : Fin n, Umat b j l • gs b l =
      ∑ l ∈ Finset.Iio j, mu b j l • gs b l + gs b j := by
    simp only [Umat, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
      one_smul]
    rw [Finset.sum_ite_eq' Finset.univ j (fun l => gs b l)]
    simp only [Finset.mem_univ, if_true]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext x; simp
  rw [h2]; rw [add_comm]; exact h1

lemma Umat_zero (b : Fin n → Vec n) {j l : Fin n} (h : j < l) : Umat b j l = 0 := by
  simp [Umat, not_lt.2 h.le, h.ne']

lemma Umat_diag (b : Fin n → Vec n) (j : Fin n) : Umat b j j = 1 := by
  simp [Umat]

lemma inner_b (b : Fin n → Vec n) (j k : Fin n) :
    inner ℝ (b j) (b k) = ∑ l, Umat b j l * Umat b k l * inner ℝ (gs b l) (gs b l) := by
  have h1 := b_eq_U b j
  have h2 := b_eq_U b k
  calc inner ℝ (b j) (b k)
      = inner ℝ (∑ a : Fin n, Umat b j a • gs b a) (∑ c : Fin n, Umat b k c • gs b c) := by
        rw [← h1, ← h2]
    _ = _ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finset.sum_eq_single a]
      · ring
      · intro c _ hc
        rw [gs_orth b hc.symm]; ring
      · simp

lemma sum_castLE {i : ℕ} (h : i ≤ n) (f : Fin n → ℝ) (hf : ∀ l : Fin n, i ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ a : Fin i, f (Fin.castLE h a) := by
  have e := Finset.sum_map Finset.univ (Fin.castLEEmb h) f
  have e' : ∑ a : Fin i, f (Fin.castLEEmb h a) = ∑ a : Fin i, f (Fin.castLE h a) := rfl
  rw [← e', ← e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  apply hf
  by_contra hlt
  rw [not_le] at hlt
  apply hl
  rw [Finset.mem_map]
  exact ⟨⟨l.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem gram_eq_prod (b : Fin n → Vec n) (i : ℕ) (h : i ≤ n) :
    gram b i = ∏ a : Fin i, inner ℝ (gs b (Fin.castLE h a)) (gs b (Fin.castLE h a)) := by
  unfold gram
  rw [dif_pos h]
  set Ui : Matrix (Fin i) (Fin i) ℝ := Matrix.of fun j a => Umat b (Fin.castLE h j) (Fin.castLE h a)
    with hUi
  set D : Matrix (Fin i) (Fin i) ℝ := Matrix.diagonal fun a =>
    inner ℝ (gs b (Fin.castLE h a)) (gs b (Fin.castLE h a)) with hD
  have hmat : (Matrix.of fun (j l : Fin i) => inner ℝ (b (Fin.castLE h j)) (b (Fin.castLE h l)))
      = Ui * D * Ui.transpose := by
    ext j k
    rw [Matrix.of_apply, inner_b]
    rw [sum_castLE h]
    · rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hD, Matrix.mul_diagonal]
      simp [hUi]
      ring
    · intro l hl
      have : Fin.castLE h j < l := by
        rw [Fin.lt_def]; simp; have := j.2; omega
      rw [Umat_zero b this]; ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hD, Matrix.det_diagonal]
  have hdet : Ui.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [hUi, Umat_diag]
    · intro j a hja
      have hja' : j < a := hja
      simp only [hUi, Matrix.of_apply]
      apply Umat_zero
      rw [Fin.lt_def]; simpa using hja'
  rw [hdet]; ring


theorem gram_succ (b : Fin n → Vec n) (m : ℕ) (h : m + 1 ≤ n) :
    gram b (m + 1) = gram b m * ‖gs b ⟨m, by omega⟩‖ ^ 2 := by
  rw [gram_eq_prod b (m + 1) h, gram_eq_prod b m (by omega), Fin.prod_univ_castSucc]
  congr 1
  simp only [real_inner_self_eq_norm_sq]
  rfl

theorem gram_pos (b : Fin n → Vec n) (hb : LinearIndependent ℝ b) (i : ℕ) (h : i ≤ n) :
    0 < gram b i := by
  rw [gram_eq_prod b i h]
  apply Finset.prod_pos
  intro a _
  rw [real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero _ hb)) 2

theorem gram_congr_gs (b b' : Fin n → Vec n) (hgs : ∀ l, gs b' l = gs b l) (i : ℕ) (h : i ≤ n) :
    gram b' i = gram b i := by
  rw [gram_eq_prod b i h, gram_eq_prod b' i h]
  simp only [hgs]

theorem gram_prefix (b b' : Fin n → Vec n) (i : ℕ) (hbb : ∀ j : Fin n, j.val < i → b' j = b j) :
    gram b' i = gram b i := by
  unfold gram
  by_cases h : i ≤ n
  · rw [dif_pos h, dif_pos h]
    congr 1
    ext j l
    simp only [Matrix.of_apply]
    rw [hbb _ (by simp), hbb _ (by simp)]
  · rw [dif_neg h, dif_neg h]

theorem gram_swap (b : Fin n → Vec n) (p q : Fin n) (i : ℕ) (hi : i ≤ n)
    (hp : p.val < i) (hq : q.val < i) :
    gram (b ∘ Equiv.swap p q) i = gram b i := by
  unfold gram
  rw [dif_pos hi, dif_pos hi]
  let e : Equiv.Perm (Fin i) := Equiv.swap ⟨p.val, hp⟩ ⟨q.val, hq⟩
  have hc : ∀ x : Fin i, Fin.castLE hi (e x) = Equiv.swap p q (Fin.castLE hi x) := by
    intro x
    have hinj : Function.Injective (Fin.castLE hi) := Fin.castLE_injective hi
    have := hinj.map_swap (⟨p.val, hp⟩ : Fin i) ⟨q.val, hq⟩ x
    exact this
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Function.comp]
  rw [hc, hc, Equiv.swap_apply_self, Equiv.swap_apply_self]


lemma gs_swap (c : Fin n → Vec n) (p q : Fin n) (hpq : q.val = p.val + 1) :
    gs (c ∘ Equiv.swap p q) p = gs c q + mu c q p • gs c p := by
  have hpq' : p < q := by rw [Fin.lt_def]; omega
  have hfix : ∀ x : Fin n, x < p → (c ∘ Equiv.swap p q) x = c x := by
    intro x hx
    have h1 : x ≠ p := hx.ne
    have h2 : x ≠ q := (hx.trans hpq').ne
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hg : ∀ j : Fin n, j < p → gs (c ∘ Equiv.swap p q) j = gs c j := fun j hj =>
    gs_prefix c _ j (fun x hx => hfix x (lt_of_le_of_lt hx hj)) j le_rfl
  have hcp : (c ∘ Equiv.swap p q) p = c q := by simp [Function.comp]
  have e1 := b_eq (c ∘ Equiv.swap p q) p
  have e2 := b_eq c q
  have hI : Finset.Iio q = insert p (Finset.Iio p) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
    omega
  rw [hI, Finset.sum_insert (by simp)] at e2
  have e3 : ∑ j ∈ Finset.Iio p, mu (c ∘ Equiv.swap p q) p j • gs (c ∘ Equiv.swap p q) j =
      ∑ j ∈ Finset.Iio p, mu c q j • gs c j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < p := Finset.mem_Iio.1 hj
    rw [mu_eq, mu_eq, hg j hj', hcp]
  rw [e3, hcp] at e1
  -- e1 : c q = gs c' p + Σ, e2 : c q = gs c q + (mu • gs c p + Σ)
  have : gs (c ∘ Equiv.swap p q) p = c q - ∑ j ∈ Finset.Iio p, mu c q j • gs c j := by
    rw [eq_sub_iff_add_eq]; exact e1.symm
  rw [this]
  nth_rewrite 1 [e2]
  abel


lemma case1_core (b b'' b' : Fin n → Vec n) (m : ℕ) (hm : m + 2 ≤ n)
    (hb : LinearIndependent ℝ b)
    (hne : ∀ j : Fin n, j.val ≠ m + 1 → b'' j = b j)
    (hgs : ∀ i, gs b'' i = gs b i)
    (h119 : ‖gs b'' ⟨m + 1, by omega⟩ + mu b'' ⟨m + 1, by omega⟩ ⟨m, by omega⟩ •
        gs b'' ⟨m, by omega⟩‖ ^ 2 < (3 / 4 : ℝ) * ‖gs b'' ⟨m, by omega⟩‖ ^ 2)
    (hb' : b' = b'' ∘ Equiv.swap (⟨m, by omega⟩ : Fin n) ⟨m + 1, by omega⟩) :
    gram b' (m + 1) < (3 / 4 : ℝ) * gram b (m + 1) ∧
      ∀ i, i ≤ n → i ≠ m + 1 → gram b' i = gram b i := by
  have g1 : gram b'' (m + 1) = gram b (m + 1) :=
    gram_prefix b b'' (m + 1) (fun j hj => hne j (by omega))
  have g2 : gram b'' m = gram b m := gram_prefix b b'' m (fun j hj => hne j (by omega))
  have g3 : gram b' m = gram b m := by
    rw [← g2]
    refine gram_prefix b'' b' m (fun j hj => ?_)
    rw [hb']
    have h1 : j ≠ (⟨m, by omega⟩ : Fin n) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have h2 : j ≠ (⟨m + 1, by omega⟩ : Fin n) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp [Function.comp, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hpos : 0 < gram b m := gram_pos b hb m (by omega)
  have s1 := gram_succ b' m (by omega)
  have s2 := gram_succ b'' m (by omega)
  have hs := gs_swap b'' (⟨m, by omega⟩ : Fin n) ⟨m + 1, by omega⟩ rfl
  rw [← hb'] at hs
  constructor
  · rw [s1, g3, hs, ← g1, s2, g2]
    nlinarith [mul_pos hpos hpos, hpos, h119]
  · intro i hi hne1
    by_cases hlt : i ≤ m
    · refine gram_prefix b b' i (fun j hj => ?_)
      rw [hb']
      have h1 : j ≠ (⟨m, by omega⟩ : Fin n) := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      have h2 : j ≠ (⟨m + 1, by omega⟩ : Fin n) := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hne j (by omega)
    · have : gram b' i = gram b'' i := by
        rw [hb']; exact gram_swap b'' _ _ i hi (by simp; omega) (by simp; omega)
      rw [this]
      exact gram_congr_gs b b'' hgs i hi

lemma potD_lt (b b' : Fin n → Vec n) (hb : LinearIndependent ℝ b) (c : ℕ) (hc : 0 < c ∧ c < n)
    (h1 : gram b' c < (3 / 4 : ℝ) * gram b c) (h2 : ∀ i, i ≤ n → i ≠ c → gram b' i = gram b i) :
    potD b' < (3 / 4 : ℝ) * potD b := by
  unfold potD
  have hcS : c ∈ Finset.Ioo 0 n := Finset.mem_Ioo.2 hc
  rw [← Finset.mul_prod_erase _ _ hcS, ← Finset.mul_prod_erase _ (fun i => gram b i) hcS]
  have hprod : ∏ i ∈ (Finset.Ioo 0 n).erase c, gram b' i =
      ∏ i ∈ (Finset.Ioo 0 n).erase c, gram b i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    exact h2 i (by have := (Finset.mem_Ioo.1 (Finset.mem_of_mem_erase hi)).2; omega)
      (Finset.ne_of_mem_erase hi)
  have hP : 0 < ∏ i ∈ (Finset.Ioo 0 n).erase c, gram b i := by
    apply Finset.prod_pos
    intro i hi
    exact gram_pos b hb i (by have := (Finset.mem_Ioo.1 (Finset.mem_of_mem_erase hi)).2; omega)
  rw [hprod]
  nlinarith

theorem potD_core {n : ℕ} (b b' : Fin n → Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) :
    (Case1 (b, k) (b', k') →
      gram b' (k - 1) < (3 / 4 : ℝ) * gram b (k - 1) ∧
      (∀ i : ℕ, i ≤ n → i ≠ k - 1 → gram b' i = gram b i) ∧
      potD b' < (3 / 4 : ℝ) * potD b) ∧
    (Case2 (b, k) (b', k') → ∀ i : ℕ, i ≤ n → gram b' i = gram b i) := by
  constructor
  · intro h
    obtain ⟨hk, b'', h118, h119, hb', hk'⟩ := h
    have hk1 : 2 ≤ k := hk.1
    have hk2 : k ≤ n := hk.2
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    obtain ⟨_, h119⟩ := h119
    have key := case1_core b b'' b' m (by omega) hb
      (fun j hj => achieve118_ne h118 j (by omega)) (achieve118_gs h118) h119 hb'
    have e : m + 2 - 1 = m + 1 := rfl
    rw [e]
    refine ⟨key.1, key.2, ?_⟩
    exact potD_lt b b' hb (m + 1) ⟨by omega, by omega⟩ key.1 key.2
  · intro h i hi
    obtain ⟨hk, b'', h118, hc, hloop, hbig, hk'⟩ := h
    obtain ⟨g1, g2, g3⟩ := loop_props hloop
    exact gram_congr_gs b b' (fun l => (g1 l).trans (achieve118_gs h118 l)) i hi

end Gram
end LLLFactor.Reduction

open LLLFactor.Reduction


theorem solution {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) :
    (Case1 (b, k) (b', k') →
      gram b' (k - 1) < (3 / 4 : ℝ) * gram b (k - 1) ∧
      (∀ i : ℕ, i ≤ n → i ≠ k - 1 → gram b' i = gram b i) ∧
      potD b' < (3 / 4 : ℝ) * potD b) ∧
    (Case2 (b, k) (b', k') → ∀ i : ℕ, i ≤ n → gram b' i = gram b i) := by
  exact potD_core b b' k k' hb
