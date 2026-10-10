-- Prove2me | solution 1 for LLLFactor.Reduction.algorithm_terminates
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T04:00:45.900386+00:00
-- url     : https://prove2.me/submissions/2612e709-4409-4224-964a-acefdc9f43fe

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

/- BEGIN WHOLE MODULE GramChange -/
section
namespace LLLFactor.Reduction.Proof
open scoped InnerProductSpace
open Finset Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_sum_smul {m : ℕ} (v : Fin m → E) (T : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.gram ℝ (fun i => ∑ j, T i j • v j) = T * Matrix.gram ℝ v * T.transpose := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma det_gram_sum_smul {m : ℕ} (v : Fin m → E)
    (T : Matrix (Fin m) (Fin m) ℝ) (hT : T.det = 1) :
    (Matrix.gram ℝ (fun i => ∑ j, T i j • v j)).det = (Matrix.gram ℝ v).det := by
  rw [gram_sum_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  ring

lemma gram_det_pos {m : ℕ} (v : Fin m → E) (hv : LinearIndependent ℝ v) :
    0 < (Matrix.gram ℝ v).det :=
  (Matrix.posDef_gram_iff_linearIndependent.mpr hv).det_pos

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramChange -/

/- BEGIN WHOLE MODULE GramSchmidtMatrix -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace
open Finset Matrix

noncomputable def gsMatrix {n m : ℕ} (b : Fin n → Vec n) (h : m ≤ n) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if j < i then mu b (Fin.castLE h i) (Fin.castLE h j)
    else if j = i then 1 else 0

lemma gsMatrix_det {n m : ℕ} (b : Fin n → Vec n) (h : m ≤ n) :
    (gsMatrix b h).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [gsMatrix]
  · intro i j hij
    change i < j at hij
    simp [gsMatrix, not_lt.mpr (le_of_lt hij), ne_of_gt hij]

lemma gs_expansion {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ j ∈ Iio i, mu b i j • gs b j := by
  convert InnerProductSpace.gramSchmidt_def'' ℝ b i using 1
  congr 1
  apply sum_congr rfl
  intro j hj
  congr 1
  simp only [mu, gs, real_inner_self_eq_norm_sq, real_inner_comm, RCLike.ofReal_real_eq_id, id_eq]

lemma gs_prefix_sum {n m : ℕ} (b : Fin n → Vec n) (h : m ≤ n) (i : Fin m) :
    (∑ j ∈ Iio (Fin.castLE h i), mu b (Fin.castLE h i) j • gs b j) =
    ∑ j ∈ Iio i, mu b (Fin.castLE h i) (Fin.castLE h j) • gs b (Fin.castLE h j) := by
  symm
  apply sum_bij (fun j _ => Fin.castLE h j)
  · intro j hj; simpa using hj
  · intro j hj k hk heq; exact Fin.castLE_injective h heq
  · intro j hj
    refine ⟨⟨j.val, by have hh := Finset.mem_Iio.mp hj; exact Nat.lt_trans hh i.isLt⟩, ?_, ?_⟩
    · apply Finset.mem_Iio.mpr
      have hh := Finset.mem_Iio.mp hj
      change j.val < i.val at hh
      exact hh
    · rfl
  · intro j hj; rfl

lemma gsMatrix_representation {n m : ℕ} (b : Fin n → Vec n) (h : m ≤ n) (i : Fin m) :
    b (Fin.castLE h i) = ∑ j, gsMatrix b h i j • gs b (Fin.castLE h j) := by
  change b (Fin.castLE h i) = ∑ j, (if j < i then mu b (Fin.castLE h i) (Fin.castLE h j) else if j = i then 1 else 0) • gs b (Fin.castLE h j)
  rw [gs_expansion b (Fin.castLE h i), gs_prefix_sum b h i]
  simp only [ite_smul, one_smul, zero_smul]
  rw [sum_ite, sum_ite]
  simp only [sum_const_zero, add_zero]
  rw [show univ.filter (fun j : Fin m => j < i) = Iio i by ext; simp]
  rw [Finset.sum_filter]
  simp [add_comm]

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramSchmidtMatrix -/

/- BEGIN WHOLE MODULE GramProduct -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace
open Finset Matrix

lemma gram_eq_prod_gs {n : ℕ} (b : Fin n → Vec n) {m : ℕ} (h : m ≤ n) :
    gram b m = ∏ j : Fin m, ‖gs b (Fin.castLE h j)‖ ^ 2 := by
  have hr : (fun i : Fin m => b (Fin.castLE h i)) =
      fun i => ∑ j, gsMatrix b h i j • gs b (Fin.castLE h j) := by
    funext i; exact gsMatrix_representation b h i
  have hd : Matrix.gram ℝ (fun j : Fin m => gs b (Fin.castLE h j)) =
      Matrix.diagonal (fun j => ‖gs b (Fin.castLE h j)‖ ^ 2) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp only [Matrix.gram_apply, Matrix.diagonal_apply, if_neg hij]
      exact InnerProductSpace.gramSchmidt_orthogonal ℝ b
        (fun heq => hij (Fin.castLE_injective h heq))
  change (if hm : m ≤ n then _ else _) = _
  rw [dif_pos h]
  change (Matrix.gram ℝ (fun i : Fin m => b (Fin.castLE h i))).det = _
  rw [hr, det_gram_sum_smul _ _ (gsMatrix_det b h), hd, Matrix.det_diagonal]

lemma gram_map_eq_gs_map {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L : Vec n →ₗ[ℝ] E) (b : Fin n → Vec n)
    {m : ℕ} (h : m ≤ n) :
    (Matrix.gram ℝ (fun i : Fin m => L (b (Fin.castLE h i)))).det =
      (Matrix.gram ℝ (fun i : Fin m => L (gs b (Fin.castLE h i)))).det := by
  have hr : (fun i : Fin m => L (b (Fin.castLE h i))) =
      fun i => ∑ j, gsMatrix b h i j • L (gs b (Fin.castLE h j)) := by
    funext i
    rw [gsMatrix_representation b h i, map_sum]
    simp
  rw [hr, det_gram_sum_smul _ _ (gsMatrix_det b h)]

lemma gram_pos {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
    {m : ℕ} (h : m ≤ n) : 0 < gram b m := by
  rw [gram, dif_pos h]
  apply gram_det_pos
  exact hb.comp (Fin.castLE h) (Fin.castLE_injective h)

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramProduct -/

/- BEGIN WHOLE MODULE GSPrefix -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace

noncomputable def prefixSpan {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    Submodule ℝ (Vec n) := Submodule.span ℝ (b '' Set.Iio i)

lemma gs_sub_mem_prefix {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    b i - gs b i ∈ prefixSpan b i := by
  rw [prefixSpan, ← InnerProductSpace.span_gramSchmidt_Iio ℝ b i]
  rw [gs, InnerProductSpace.gramSchmidt_def'' ℝ b i]
  simp only [add_sub_cancel_left]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, Finset.mem_Iio.mp hj, rfl⟩

lemma gs_orthogonal_prefix {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
    gs b i ∈ (prefixSpan b i)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact InnerProductSpace.gramSchmidt_inv_triangular ℝ b hj
  | zero => simp
  | add x y hx hy hxi hyi => simp [inner_add_right, hxi, hyi]
  | smul a x hx hxi => simp [inner_smul_right, hxi]

lemma gs_residual_unique {n : ℕ} (b : Fin n → Vec n) (i : Fin n) (v : Vec n)
    (hv : b i - v ∈ prefixSpan b i) (ho : v ∈ (prefixSpan b i)ᗮ) :
    v = gs b i := by
  have hm : v - gs b i ∈ prefixSpan b i := by
    convert (prefixSpan b i).sub_mem (gs_sub_mem_prefix b i) hv using 1; abel
  have hz : v - gs b i ∈ (prefixSpan b i)ᗮ :=
    (prefixSpan b i)ᗮ.sub_mem ho (gs_orthogonal_prefix b i)
  have hzero : v - gs b i = 0 := by
    have hh : v - gs b i ∈ (prefixSpan b i) ⊓ (prefixSpan b i)ᗮ := ⟨hm,hz⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hh
  exact sub_eq_zero.mp hzero

lemma gs_eq_of_prefix {n : ℕ} (b c : Fin n → Vec n) (i : Fin n)
    (hspan : prefixSpan c i = prefixSpan b i)
    (hsub : c i - b i ∈ prefixSpan b i) : gs c i = gs b i := by
  apply gs_residual_unique b i
  · have hh := gs_sub_mem_prefix c i
    rw [hspan] at hh
    convert (prefixSpan b i).sub_mem hh hsub using 1; abel
  · rw [← hspan]
    exact gs_orthogonal_prefix c i

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GSPrefix -/

/- BEGIN WHOLE MODULE ReductionBasis -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma reduceBy_apply_self {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    reduceBy b κ l r κ = b κ - (r : ℝ) • b l := by simp [reduceBy]

lemma reduceBy_apply_of_ne {n : ℕ} (b : Fin n → Vec n) {κ l j : Fin n}
    (r : ℤ) (hj : j ≠ κ) : reduceBy b κ l r j = b j := by simp [reduceBy, hj]

lemma reduceBy_inverse {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l ≠ κ) (r : ℤ) : reduceBy (reduceBy b κ l r) κ l (-r) = b := by
  funext j
  by_cases hj : j = κ
  · subst j
    simp [reduceBy, h, sub_eq_add_neg]
  · simp [reduceBy, hj]

lemma reduceBy_independent {n : ℕ} {b : Fin n → Vec n}
    (hb : LinearIndependent ℝ b) {κ l : Fin n} (h : l ≠ κ) (r : ℤ) :
    LinearIndependent ℝ (reduceBy b κ l r) := by
  have heq : reduceBy b κ l r = b + (fun j => (if j = κ then -(r : ℝ) else 0) • b l) := by
    funext j
    by_cases hj : j = κ <;> simp [reduceBy, hj, sub_eq_add_neg]
  rw [heq]
  exact (linearIndependent_add_smul_iff (by simp [h])).mpr hb

lemma reduceBy_lattice_le {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    latticeOf (reduceBy b κ l r) ≤ latticeOf b := by
  apply Submodule.span_le.mpr
  rintro x ⟨j,rfl⟩
  by_cases hj : j = κ
  · subst j
    rw [reduceBy_apply_self]
    have hκ : b κ ∈ latticeOf b := Submodule.subset_span ⟨κ,rfl⟩
    have hl : b l ∈ latticeOf b := Submodule.subset_span ⟨l,rfl⟩
    have hh := (latticeOf b).sub_mem hκ ((latticeOf b).smul_mem r hl)
    rw [Int.cast_smul_eq_zsmul ℝ r (b l)]
    exact hh
  · rw [reduceBy_apply_of_ne b r hj]
    exact Submodule.subset_span ⟨j,rfl⟩

lemma reduceBy_lattice {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l ≠ κ) (r : ℤ) : latticeOf (reduceBy b κ l r) = latticeOf b := by
  apply le_antisymm (reduceBy_lattice_le b κ l r)
  have hh := reduceBy_lattice_le (reduceBy b κ l r) κ l (-r)
  rwa [reduceBy_inverse b h r] at hh

lemma reduceBy_prefix_le {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l < κ) (r : ℤ) (i : Fin n) :
    prefixSpan (reduceBy b κ l r) i ≤ prefixSpan b i := by
  apply Submodule.span_le.mpr
  rintro x ⟨j,hj,rfl⟩
  by_cases hjκ : j = κ
  · subst j
    rw [reduceBy_apply_self]
    exact (prefixSpan b i).sub_mem
      (Submodule.subset_span ⟨κ,hj,rfl⟩)
      ((prefixSpan b i).smul_mem _ (Submodule.subset_span ⟨l,h.trans hj,rfl⟩))
  · rw [reduceBy_apply_of_ne b r hjκ]
    exact Submodule.subset_span ⟨j,hj,rfl⟩

lemma reduceBy_prefix {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l < κ) (r : ℤ) (i : Fin n) :
    prefixSpan (reduceBy b κ l r) i = prefixSpan b i := by
  apply le_antisymm (reduceBy_prefix_le b h r i)
  have hh := reduceBy_prefix_le (reduceBy b κ l r) h (-r) i
  rwa [reduceBy_inverse b h.ne r] at hh

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE ReductionBasis -/

/- BEGIN WHOLE MODULE ReductionGS -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace

lemma gs_reduceBy {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l < κ) (r : ℤ) (i : Fin n) : gs (reduceBy b κ l r) i = gs b i := by
  apply gs_eq_of_prefix b _ i (reduceBy_prefix b h r i)
  by_cases hi : i = κ
  · subst i
    rw [reduceBy_apply_self]
    have hh := (prefixSpan b κ).smul_mem (-(r : ℝ))
      (Submodule.subset_span ⟨l,h,rfl⟩)
    convert hh using 1; module
  · rw [reduceBy_apply_of_ne b r hi, sub_self]
    exact (prefixSpan b i).zero_mem

lemma mu_self {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b) (i : Fin n) :
    mu b i i = 1 := by
  have hh := Submodule.inner_right_of_mem_orthogonal
    (gs_sub_mem_prefix b i) (gs_orthogonal_prefix b i)
  have he : inner ℝ (b i) (gs b i) = inner ℝ (gs b i) (gs b i) := by
    simpa only [inner_sub_left, sub_eq_zero] using hh
  rw [mu, he]
  apply div_self
  exact inner_self_ne_zero.mpr (InnerProductSpace.gramSchmidt_ne_zero i hb)

lemma mu_eq_zero_of_lt {n : ℕ} (b : Fin n → Vec n) {i j : Fin n} (h : i < j) :
    mu b i j = 0 := by
  have hh := InnerProductSpace.gramSchmidt_inv_triangular ℝ b h
  have he : inner ℝ (b i) (gs b j) = 0 := by
    change inner ℝ (b i) (InnerProductSpace.gramSchmidt ℝ b j) = 0
    rw [real_inner_comm]
    exact hh
  simp [mu, he]

lemma mu_reduceBy_self {n : ℕ} (b : Fin n → Vec n) {κ l : Fin n}
    (h : l < κ) (r : ℤ) (j : Fin n) :
    mu (reduceBy b κ l r) κ j = mu b κ j - (r : ℝ) * mu b l j := by
  simp only [mu, gs_reduceBy b h r, reduceBy_apply_self, inner_sub_left,
    real_inner_smul_left]
  ring

lemma mu_reduceBy_of_ne {n : ℕ} (b : Fin n → Vec n) {κ l i : Fin n}
    (h : l < κ) (r : ℤ) (hi : i ≠ κ) (j : Fin n) :
    mu (reduceBy b κ l r) i j = mu b i j := by
  simp only [mu, gs_reduceBy b h r, reduceBy_apply_of_ne b r hi]

lemma mu_reduceBy_target {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
    {κ l : Fin n} (h : l < κ) (r : ℤ) :
    mu (reduceBy b κ l r) κ l = mu b κ l - r := by
  rw [mu_reduceBy_self b h r, mu_self hb, mul_one]

lemma mu_reduceBy_above {n : ℕ} (b : Fin n → Vec n) {κ l j : Fin n}
    (h : l < κ) (r : ℤ) (hj : l < j) :
    mu (reduceBy b κ l r) κ j = mu b κ j := by
  rw [mu_reduceBy_self b h r, mu_eq_zero_of_lt b hj, mul_zero, sub_zero]

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE ReductionGS -/

/- BEGIN WHOLE MODULE AdjacentGS -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace

lemma gs_expand {n : ℕ} (c : Fin n → Vec n) (i : Fin n) :
    c i = gs c i + ∑ j ∈ Finset.Iio i, mu c i j • gs c j := by
  simpa [gs, mu, real_inner_comm, real_inner_self_eq_norm_sq] using
    InnerProductSpace.gramSchmidt_def'' ℝ c i

lemma prefix_congr {n : ℕ} (c d : Fin n → Vec n) (i : Fin n)
    (h : ∀ j, j < i → c j = d j) : prefixSpan c i = prefixSpan d i := by
  unfold prefixSpan
  congr 1
  ext x
  constructor <;> rintro ⟨j,hj,rfl⟩
  · exact ⟨j,hj,(h j hj).symm⟩
  · exact ⟨j,hj,h j hj⟩

lemma gs_congr_upto {n : ℕ} (c d : Fin n → Vec n) (i : Fin n)
    (h : ∀ j, j ≤ i → c j = d j) : gs c i = gs d i := by
  apply gs_eq_of_prefix d c i
  · exact prefix_congr c d i (fun j hj => h j hj.le)
  · rw [h i le_rfl, sub_self]
    exact (prefixSpan d i).zero_mem

lemma swap_prefix {n : ℕ} (c : Fin n → Vec n) {a b : Fin n} (hab : a < b) :
    prefixSpan (c ∘ Equiv.swap a b) a = prefixSpan c a := by
  apply prefix_congr
  intro j hj
  simp [Equiv.swap_apply_of_ne_of_ne hj.ne (hj.trans hab).ne]

lemma gs_swap_before {n : ℕ} (c : Fin n → Vec n) {a b i : Fin n}
    (hab : a < b) (hi : i < a) : gs (c ∘ Equiv.swap a b) i = gs c i := by
  apply gs_congr_upto
  intro j hj
  simp [Equiv.swap_apply_of_ne_of_ne (hj.trans_lt hi).ne
    ((hj.trans_lt hi).trans hab).ne]

lemma gs_swap_first {n : ℕ} (c : Fin n → Vec n) {a b : Fin n}
    (hab : (a : ℕ) + 1 = b) :
    gs (c ∘ Equiv.swap a b) a = gs c b + mu c b a • gs c a := by
  have halt : a < b := by omega
  symm
  apply gs_residual_unique (c ∘ Equiv.swap a b) a
  · rw [swap_prefix c halt]
    simp only [Function.comp_apply, Equiv.swap_apply_left]
    have ha : a ∈ Finset.Iio b := Finset.mem_Iio.mpr halt
    have hsum := Finset.sum_erase_add (Finset.Iio b) (fun j => mu c b j • gs c j) ha
    have heq : c b - (gs c b + mu c b a • gs c a) =
        ∑ j ∈ (Finset.Iio b).erase a, mu c b j • gs c j := by
      rw [gs_expand c b, ← hsum]
      abel
    rw [heq]
    apply Submodule.sum_mem
    intro j hj
    obtain ⟨hja,hjb⟩ := Finset.mem_erase.mp hj
    have hjlt : j < a := by have := Finset.mem_Iio.mp hjb; omega
    apply Submodule.smul_mem
    rw [prefixSpan, ← InnerProductSpace.span_gramSchmidt_Iio ℝ c a]
    exact Submodule.subset_span ⟨j,hjlt,rfl⟩
  · rw [swap_prefix c halt]
    apply (prefixSpan c a)ᗮ.add_mem
    · rw [Submodule.mem_orthogonal']
      intro x hx
      have hle : prefixSpan c a ≤ prefixSpan c b :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio halt.le))
      exact ((prefixSpan c b).mem_orthogonal' _).mp (gs_orthogonal_prefix c b) x (hle hx)
    · exact (prefixSpan c a)ᗮ.smul_mem _ (gs_orthogonal_prefix c a)

lemma swap_independent {n : ℕ} {c : Fin n → Vec n} (hc : LinearIndependent ℝ c)
    (a b : Fin n) : LinearIndependent ℝ (c ∘ Equiv.swap a b) :=
  hc.comp _ (Equiv.swap a b).injective

lemma swap_lattice {n : ℕ} (c : Fin n → Vec n) (a b : Fin n) :
    latticeOf (c ∘ Equiv.swap a b) = latticeOf c := by
  unfold latticeOf
  rw [Set.range_comp, (Equiv.swap a b).surjective.range_eq, Set.image_univ]

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE AdjacentGS -/

/- BEGIN WHOLE MODULE GramSwap -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open Finset Matrix

lemma gram_swap_before {n : ℕ} (c : Fin n → Vec n) {a b : Fin n}
    (hab : a < b) {m : ℕ} (hm : m ≤ a.val) :
    gram (c ∘ Equiv.swap a b) m = gram c m := by
  have hmn : m ≤ n := hm.trans a.isLt.le
  rw [gram, gram, dif_pos hmn, dif_pos hmn]
  congr 1
  ext i j
  have hi : (Fin.castLE hmn i : Fin n) < a := by
    change i.val < a.val
    omega
  have hj : (Fin.castLE hmn j : Fin n) < a := by
    change j.val < a.val
    omega
  simp [Equiv.swap_apply_of_ne_of_ne hi.ne (hi.trans hab).ne,
    Equiv.swap_apply_of_ne_of_ne hj.ne (hj.trans hab).ne]

lemma gram_swap_after {n : ℕ} (c : Fin n → Vec n) {a b : Fin n}
    {m : ℕ} (ha : a.val < m) (hb : b.val < m) (hm : m ≤ n) :
    gram (c ∘ Equiv.swap a b) m = gram c m := by
  let e : Equiv.Perm (Fin m) := Equiv.swap ⟨a.val,ha⟩ ⟨b.val,hb⟩
  have he (i : Fin m) : Equiv.swap a b (Fin.castLE hm i) = Fin.castLE hm (e i) := by
    by_cases hia : i.val = a.val
    · have hi : i = ⟨a.val,ha⟩ := Fin.ext hia
      subst i
      simp [e]
    · by_cases hib : i.val = b.val
      · have hi : i = ⟨b.val,hb⟩ := Fin.ext hib
        subst i
        simp [e]
      · have h1 : (Fin.castLE hm i : Fin n) ≠ a := fun h => hia (congrArg Fin.val h)
        have h2 : (Fin.castLE hm i : Fin n) ≠ b := fun h => hib (congrArg Fin.val h)
        simp [e, Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne (show i ≠ ⟨a.val,ha⟩ from fun h => hia (congrArg Fin.val h))
            (show i ≠ ⟨b.val,hb⟩ from fun h => hib (congrArg Fin.val h))]
  rw [gram, gram, dif_pos hm, dif_pos hm]
  change (Matrix.gram ℝ (fun i : Fin m => c (Equiv.swap a b (Fin.castLE hm i)))).det = _
  simp_rw [he]
  exact Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ (fun i : Fin m => c (Fin.castLE hm i)))

lemma gram_swap_unchanged {n : ℕ} (c : Fin n → Vec n) {a b : Fin n}
    (hab : a.val+1=b.val) {m : ℕ} (hm : m ≤ n) (hne : m ≠ a.val+1) :
    gram (c ∘ Equiv.swap a b) m = gram c m := by
  by_cases hh : m ≤ a.val
  · exact gram_swap_before c (by omega) hh
  · exact gram_swap_after c (by omega) (by omega) hm

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramSwap -/

/- BEGIN WHOLE MODULE GramStep -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open Finset

lemma gram_succ {n : ℕ} (c : Fin n → Vec n) {m : ℕ} (hm : m < n) :
    gram c (m+1) = gram c m * ‖gs c ⟨m,hm⟩‖^2 := by
  rw [gram_eq_prod_gs c (Nat.succ_le_iff.mpr hm), Fin.prod_univ_castSucc,
    gram_eq_prod_gs c hm.le]
  rfl

lemma gram_reduceBy {n : ℕ} (c : Fin n → Vec n) {κ l : Fin n}
    (hl : l < κ) (r : ℤ) (m : ℕ) :
    gram (reduceBy c κ l r) m = gram c m := by
  by_cases hm : m ≤ n
  · rw [gram_eq_prod_gs _ hm, gram_eq_prod_gs _ hm]
    apply prod_congr rfl
    intro i hi
    rw [gs_reduceBy c hl r]
  · simp [gram, hm]

lemma gram_swap_decrease {n : ℕ} (c : Fin n → Vec n)
    (hc : LinearIndependent ℝ c) {a b : Fin n} (hab : a.val+1=b.val)
    (hsmall : ‖gs c b + mu c b a • gs c a‖^2 < (3/4:ℝ)*‖gs c a‖^2) :
    gram (c ∘ Equiv.swap a b) (a.val+1) < (3/4:ℝ)*gram c (a.val+1) := by
  rw [gram_succ _ a.isLt, gram_succ _ a.isLt]
  have hpre := gram_swap_before c (show a < b by omega) (m:=a.val) le_rfl
  rw [hpre]
  have hgs := gs_swap_first c hab
  change gs (c ∘ Equiv.swap a b) ⟨a.val,a.isLt⟩ = _ at hgs
  rw [hgs]
  have hp : 0 < gram c a.val := gram_pos c hc a.isLt.le
  nlinarith [mul_lt_mul_of_pos_left hsmall hp]

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramStep -/

/- BEGIN WHOLE MODULE AchieveGS -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma achieve_gs {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (h : Achieve118 b k c) (i : Fin n) : gs c i = gs b i := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨_,rfl⟩ | ⟨_,r,_,rfl⟩
    · rfl
    · exact gs_reduceBy b (by change k-2 < k-1; omega) r i
  · subst c; rfl

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE AchieveGS -/

/- BEGIN WHOLE MODULE StepBasis -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma achieve_basis {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (hb : LinearIndependent ℝ b) (h : Achieve118 b k c) :
    LinearIndependent ℝ c ∧ latticeOf c = latticeOf b := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨_,rfl⟩ | ⟨_,r,_,rfl⟩
    · exact ⟨hb,rfl⟩
    · have hne : (⟨k-2,by omega⟩ : Fin n) ≠ ⟨k-1,by omega⟩ := by
        intro he; have := congrArg Fin.val he; dsimp at this; omega
      exact ⟨reduceBy_independent hb hne r, reduceBy_lattice b hne r⟩
  · subst c; exact ⟨hb,rfl⟩

lemma loop_basis {n : ℕ} {b c : Fin n → Vec n} {κ : Fin n}
    (hb : LinearIndependent ℝ b) (h : LoopStep κ b c) :
    LinearIndependent ℝ c ∧ latticeOf c = latticeOf b := by
  obtain ⟨l,hl,_,_,r,_,rfl⟩ := h
  exact ⟨reduceBy_independent hb hl.ne r, reduceBy_lattice b hl.ne r⟩

lemma loopStar_basis {n : ℕ} {b c : Fin n → Vec n} {κ : Fin n}
    (hb : LinearIndependent ℝ b) (h : Relation.ReflTransGen (LoopStep κ) b c) :
    LinearIndependent ℝ c ∧ latticeOf c = latticeOf b := by
  induction h with
  | refl => exact ⟨hb,rfl⟩
  | @tail c d hcd hstep ih =>
    obtain ⟨hd,heq⟩ := loop_basis ih.1 hstep
    exact ⟨hd,heq.trans ih.2⟩

lemma step_basis {n : ℕ} {s t : State n} (hs : LinearIndependent ℝ s.1)
    (h : Step s t) : LinearIndependent ℝ t.1 ∧ latticeOf t.1 = latticeOf s.1 := by
  rcases h with h | h
  · obtain ⟨hk,c,hc,_,ht,_⟩ := h
    obtain ⟨hc',heq⟩ := achieve_basis hs hc
    rw [ht]
    exact ⟨swap_independent hc' _ _, (swap_lattice c _ _).trans heq⟩
  · obtain ⟨hk,c,hc,_,hloop,_,_⟩ := h
    obtain ⟨hc',heq⟩ := achieve_basis hs hc
    obtain ⟨ht,heq'⟩ := loopStar_basis hc' hloop
    exact ⟨ht,heq'.trans heq⟩

lemma reachable_basis {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
    {s : State n} (h : Reachable b s) :
    LinearIndependent ℝ s.1 ∧ latticeOf s.1 = latticeOf b := by
  induction h with
  | refl => exact ⟨hb,rfl⟩
  | @tail s t hst hstep ih =>
    obtain ⟨ht,heq⟩ := step_basis ih.1 hstep
    exact ⟨ht,heq.trans ih.2⟩

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE StepBasis -/

/- BEGIN WHOLE MODULE PotentialStep -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open Finset

lemma potD_pos {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b) :
    0 < potD b := by
  apply prod_pos
  intro m hm
  exact gram_pos b hb (mem_Ioo.mp hm).2.le

lemma achieve_gram {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (h : Achieve118 b k c) (m : ℕ) : gram c m = gram b m := by
  by_cases hm : m ≤ n
  · rw [gram_eq_prod_gs _ hm, gram_eq_prod_gs _ hm]
    apply prod_congr rfl
    intro i hi
    rw [achieve_gs h]
  · simp [gram,hm]

lemma loopStar_gram {n : ℕ} {b c : Fin n → Vec n} {κ : Fin n}
    (h : Relation.ReflTransGen (LoopStep κ) b c) (m : ℕ) : gram c m = gram b m := by
  induction h with
  | refl => rfl
  | @tail c d hcd hs ih =>
    obtain ⟨l,hl,_,_,r,_,rfl⟩ := hs
    rw [gram_reduceBy c hl r,ih]

lemma potD_swap_decrease {n : ℕ} (c : Fin n → Vec n)
    (hc : LinearIndependent ℝ c) {a b : Fin n} (hab : a.val+1=b.val)
    (hsmall : ‖gs c b + mu c b a • gs c a‖^2 < (3/4:ℝ)*‖gs c a‖^2) :
    potD (c ∘ Equiv.swap a b) < (3/4:ℝ)*potD c := by
  have hm : a.val+1 ∈ Ioo 0 n := mem_Ioo.mpr ⟨by omega,by omega⟩
  have hp : 0 < ∏ m ∈ (Ioo 0 n).erase (a.val+1), gram c m := by
    apply prod_pos
    intro m hm
    exact gram_pos c hc (mem_Ioo.mp (mem_erase.mp hm).2).2.le
  have he : (∏ m ∈ (Ioo 0 n).erase (a.val+1), gram (c ∘ Equiv.swap a b) m) =
      ∏ m ∈ (Ioo 0 n).erase (a.val+1), gram c m := by
    apply prod_congr rfl
    intro m hm
    exact gram_swap_unchanged c hab (mem_Ioo.mp (mem_erase.mp hm).2).2.le
      (mem_erase.mp hm).1
  unfold potD
  rw [← prod_erase_mul _ _ hm, ← prod_erase_mul _ _ hm, he]
  have hh := mul_lt_mul_of_pos_left (gram_swap_decrease c hc hab hsmall) hp
  nlinarith

lemma case1_potential {n : ℕ} {s t : State n} (hs : LinearIndependent ℝ s.1)
    (h : Case1 s t) : potD t.1 < (3/4:ℝ)*potD s.1 := by
  obtain ⟨hk,c,hc,hcond,ht,_⟩ := h
  obtain ⟨_,hsmall⟩ := hcond
  rw [ht]
  have hd := potD_swap_decrease c (achieve_basis hs hc).1
    (a:=⟨s.2-2,by omega⟩) (b:=⟨s.2-1,by omega⟩) (by simp; omega) hsmall
  have he : potD c = potD s.1 := by
    apply prod_congr rfl
    intro m hm
    exact achieve_gram hc m
  rwa [he] at hd

lemma case2_potential {n : ℕ} {s t : State n} (h : Case2 s t) :
    potD t.1 = potD s.1 := by
  obtain ⟨_,c,hc,_,hloop,_,_⟩ := h
  apply prod_congr rfl
  intro m hm
  rw [loopStar_gram hloop m, achieve_gram hc m]

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE PotentialStep -/

/- BEGIN WHOLE MODULE LatticeCoordinates -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open scoped InnerProductSpace

lemma exists_lattice_coordinates {n : ℕ} (b : Fin n → Vec n)
    (hb : LinearIndependent ℝ b) :
    ∃ F : Vec n ≃L[ℝ] Vec n,
      ∀ x ∈ latticeOf b, ∀ j : Fin n, ∃ z : ℤ, (F x) j = (z : ℝ) := by
  let B : Module.Basis (Fin n) ℝ (Vec n) :=
    basisOfLinearIndependentOfCardEqFinrank' b hb (by simp [Vec])
  have hB : ∀ i, B i = b i := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' b hb _) i
  let F : Vec n ≃L[ℝ] Vec n :=
    B.equivFunL.trans (EuclideanSpace.equiv (Fin n) ℝ).symm
  refine ⟨F, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro j
    refine ⟨if i = j then 1 else 0, ?_⟩
    change B.equivFun (b i) j = _
    rw [← hB i]
    simp
  | zero => intro j; exact ⟨0, by simp⟩
  | add x y hx hy hxi hyi =>
    intro j
    obtain ⟨a, ha⟩ := hxi j
    obtain ⟨c, hc⟩ := hyi j
    refine ⟨a+c, ?_⟩
    simp [map_add, ha, hc]
  | smul a x hx hxi =>
    intro j
    obtain ⟨c, hc⟩ := hxi j
    refine ⟨a*c, ?_⟩
    simp [map_zsmul, hc]

lemma integral_gram {n m : ℕ} (v : Fin m → Vec n)
    (hv : ∀ i j, ∃ z : ℤ, v i j = (z : ℝ)) :
    ∃ z : ℤ, (Matrix.gram ℝ v).det = (z : ℝ) := by
  classical
  choose Z hZ using hv
  let G : Matrix (Fin m) (Fin m) ℤ := fun i j => ∑ k, Z i k * Z j k
  refine ⟨G.det, ?_⟩
  have hg : Matrix.gram ℝ v = G.map (Int.castRingHom ℝ) := by
    ext i j
    change inner ℝ (v i) (v j) = ((∑ k, Z i k * Z j k : ℤ) : ℝ)
    simp [PiLp.inner_apply, hZ, mul_comm]
  rw [hg]
  exact ((Int.castRingHom ℝ).map_det G).symm

lemma integral_gram_one_le {n m : ℕ} (v : Fin m → Vec n)
    (hlin : LinearIndependent ℝ v) (hv : ∀ i j, ∃ z : ℤ, v i j = (z : ℝ)) :
    1 ≤ (Matrix.gram ℝ v).det := by
  obtain ⟨z, hz⟩ := integral_gram v hv
  have hp := gram_det_pos v hlin
  rw [hz] at hp ⊢
  have : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE LatticeCoordinates -/

/- BEGIN WHOLE MODULE GramBound -/
section
namespace LLLFactor.Reduction.Proof
open scoped InnerProductSpace
open Finset Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_det_le_factorial {m : ℕ} (v : Fin m → E) :
    (Matrix.gram ℝ v).det ≤ (m.factorial : ℝ) * ∏ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ ‖(Matrix.gram ℝ v).det‖ := le_abs_self _
    _ ≤ ∑ σ : Equiv.Perm (Fin m), ‖Equiv.Perm.sign σ • ∏ i, inner ℝ (v (σ i)) (v i)‖ := by
      rw [Matrix.det_apply]; exact norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), ∏ i, ‖v i‖ ^ 2 := by
      apply sum_le_sum
      intro σ hσ
      have hs : ‖Equiv.Perm.sign σ • ∏ i, inner ℝ (v (σ i)) (v i)‖ =
          ∏ i, ‖inner ℝ (v (σ i)) (v i)‖ := by
        rcases Int.isUnit_eq_one_or (Equiv.Perm.sign σ).isUnit with h | h <;>
          simp [Units.smul_def, h, norm_prod]
      rw [hs]
      calc
        _ ≤ ∏ i, (‖v (σ i)‖ * ‖v i‖) :=
          prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_inner_le_norm _ _)
        _ = ∏ i, ‖v i‖ ^ 2 := by
          rw [prod_mul_distrib, Equiv.prod_comp σ (fun i => ‖v i‖)]
          simp [sq, prod_mul_distrib]
    _ = _ := by simp [Fintype.card_perm, Fintype.card_fin]

lemma gram_det_le_operator {m : ℕ} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (L : E →L[ℝ] F) (v : Fin m → E)
    (K : ℝ) (hK : ‖L‖ ≤ K) :
    (Matrix.gram ℝ (fun i => L (v i))).det ≤
      (m.factorial : ℝ) * K ^ (2*m) * ∏ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ (m.factorial : ℝ) * ∏ i, ‖L (v i)‖ ^ 2 := gram_det_le_factorial _
    _ ≤ (m.factorial : ℝ) * ∏ i, (K * ‖v i‖) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply prod_le_prod (fun _ _ => sq_nonneg _)
      intro i hi
      exact pow_le_pow_left₀ (norm_nonneg _) ((L.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _))) 2
    _ = _ := by
      simp only [mul_pow, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      rw [← pow_mul]
      ring

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramBound -/

/- BEGIN WHOLE MODULE GramLowerBound -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis
open Finset

lemma lattice_gram_lower_bound {n : ℕ} (b : Fin n → Vec n)
    (hb : LinearIndependent ℝ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : Fin n → Vec n,
      LinearIndependent ℝ c → latticeOf c = latticeOf b →
      ∀ m, m ≤ n → (1 / ((m.factorial : ℝ) * K^(2*m))) ≤ gram c m := by
  obtain ⟨F, hF⟩ := exists_lattice_coordinates b hb
  let K := 1 + ‖F.toContinuousLinearMap‖
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro c hc hlat m hm
  have hmem (i : Fin m) : c (Fin.castLE hm i) ∈ latticeOf b := by
    rw [← hlat]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hi : LinearIndependent ℝ (fun i : Fin m => F (c (Fin.castLE hm i))) :=
    (hc.comp (Fin.castLE hm) (Fin.castLE_injective hm)).map' F.toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr F.injective)
  have hone := integral_gram_one_le (fun i : Fin m => F (c (Fin.castLE hm i))) hi
    (fun i j => hF _ (hmem i) j)
  change 1 ≤ (Matrix.gram ℝ (fun i : Fin m => F.toLinearEquiv.toLinearMap (c (Fin.castLE hm i)))).det at hone
  rw [gram_map_eq_gs_map F.toLinearEquiv.toLinearMap c hm] at hone
  have hu := gram_det_le_operator F.toContinuousLinearMap
    (fun i : Fin m => gs c (Fin.castLE hm i)) K (by dsimp [K]; linarith)
  rw [← gram_eq_prod_gs c hm] at hu
  have hp : 0 < (m.factorial : ℝ) * K^(2*m) := by positivity
  apply (div_le_iff₀ hp).mpr
  nlinarith [hone.trans hu]

lemma potential_uniform_lower_bound {n : ℕ} (b : Fin n → Vec n)
    (hb : LinearIndependent ℝ b) :
    ∃ d : ℝ, 0 < d ∧ ∀ c : Fin n → Vec n,
      LinearIndependent ℝ c → latticeOf c = latticeOf b → d ≤ potD c := by
  obtain ⟨K,hK,hbound⟩ := lattice_gram_lower_bound b hb
  refine ⟨∏ m ∈ Ioo 0 n, 1 / ((m.factorial : ℝ) * K^(2*m)), ?_, ?_⟩
  · apply prod_pos
    intro m hm
    positivity
  · intro c hc hlat
    apply prod_le_prod
    · intro m hm; positivity
    · intro m hm; exact hbound c hc hlat m (mem_Ioo.mp hm).2.le

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE GramLowerBound -/

/- BEGIN WHOLE MODULE LoopProgress -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma loop_complete_below {n : ℕ} (κ : Fin n) (m : ℕ) (hm : m ≤ κ.val) :
    ∀ b : Fin n → Vec n, LinearIndependent ℝ b →
    (∀ j : Fin n, m ≤ j.val → j < κ → |mu b κ j| ≤ 1/2) →
    ∃ c, Relation.ReflTransGen (LoopStep κ) b c ∧
      ∀ j : Fin n, j < κ → |mu c κ j| ≤ 1/2 := by
  induction m with
  | zero =>
    intro b _ hg
    exact ⟨b,.refl,fun j hj => hg j (Nat.zero_le _) hj⟩
  | succ m ih =>
    intro b hb hg
    let l : Fin n := ⟨m, by omega⟩
    have hlval : l.val = m := rfl
    have hl : l < κ := by omega
    have hm' : m ≤ κ.val := by omega
    by_cases hbound : |mu b κ l| ≤ 1/2
    · apply ih hm' b hb
      intro j hj hjκ
      by_cases heq : j = l
      · simpa [heq] using hbound
      · apply hg j (by have hne : j.val ≠ l.val := fun h => heq (Fin.ext h); omega) hjκ
    · have hbad : 1/2 < |mu b κ l| := lt_of_not_ge hbound
      let r : ℤ := round (mu b κ l)
      have hr : IsNearestInt r (mu b κ l) := abs_sub_round _
      let d := reduceBy b κ l r
      have hstep : LoopStep κ b d := by
        refine ⟨l,hl,hbad,?_,r,hr,rfl⟩
        intro j hj hjκ
        exact hg j (by omega) hjκ
      have hd : LinearIndependent ℝ d := reduceBy_independent hb hl.ne r
      have hgood : ∀ j : Fin n, m ≤ j.val → j < κ → |mu d κ j| ≤ 1/2 := by
        intro j hj hjκ
        by_cases heq : j = l
        · subst j
          change |mu (reduceBy b κ l r) κ l| ≤ 1/2
          rw [mu_reduceBy_target hb hl r]
          exact hr
        · have hlj : l < j := by omega
          change |mu (reduceBy b κ l r) κ j| ≤ 1/2
          rw [mu_reduceBy_above b hl r hlj]
          exact hg j (by omega) hjκ
      obtain ⟨c,hc,hfinal⟩ := ih hm' d hd hgood
      exact ⟨c,(Relation.ReflTransGen.single hstep).trans hc,hfinal⟩

lemma loop_complete {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
    (κ : Fin n) : ∃ c, Relation.ReflTransGen (LoopStep κ) b c ∧
      ∀ j : Fin n, j < κ → |mu c κ j| ≤ 1/2 := by
  apply loop_complete_below κ κ.val le_rfl b hb
  intro j hj hjκ
  omega

lemma achieve_exists {n : ℕ} (b : Fin n → Vec n) (k : ℕ) :
    ∃ c, Achieve118 b k c := by
  unfold Achieve118
  split_ifs with hk
  · by_cases h : |mu b ⟨k-1,by omega⟩ ⟨k-2,by omega⟩| ≤ 1/2
    · exact ⟨b,Or.inl ⟨h,rfl⟩⟩
    · let r : ℤ := round (mu b ⟨k-1,by omega⟩ ⟨k-2,by omega⟩)
      exact ⟨_,Or.inr ⟨lt_of_not_ge h,r,abs_sub_round _,rfl⟩⟩
  · exact ⟨b,rfl⟩

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE LoopProgress -/

/- BEGIN WHOLE MODULE LoopInvariants -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma loopStar_gs {n : ℕ} {b c : Fin n → Vec n} {κ : Fin n}
    (h : Relation.ReflTransGen (LoopStep κ) b c) (i : Fin n) : gs c i = gs b i := by
  induction h with
  | refl => rfl
  | @tail c d hcd hstep ih =>
    obtain ⟨l,hl,_,_,r,_,rfl⟩ := hstep
    exact (gs_reduceBy c hl r i).trans ih

lemma loopStar_apply {n : ℕ} {b c : Fin n → Vec n} {κ j : Fin n}
    (h : Relation.ReflTransGen (LoopStep κ) b c) (hj : j ≠ κ) : c j = b j := by
  induction h with
  | refl => rfl
  | @tail c d hcd hstep ih =>
    obtain ⟨l,_,_,_,r,_,rfl⟩ := hstep
    exact (reduceBy_apply_of_ne c r hj).trans ih

lemma loopStar_top_mu {n : ℕ} {b c : Fin n → Vec n} {κ a : Fin n}
    (ha : a.val + 1 = κ.val) (hb : |mu b κ a| ≤ 1/2)
    (h : Relation.ReflTransGen (LoopStep κ) b c) : mu c κ a = mu b κ a := by
  induction h with
  | refl => rfl
  | @tail c d hcd hstep ih =>
    obtain ⟨l,hl,hbad,_,r,_,rfl⟩ := hstep
    have hla : l < a := by
      have hne : l ≠ a := by
        intro heq; subst l; rw [ih] at hbad; exact (not_lt_of_ge hb) hbad
      omega
    exact (mu_reduceBy_above c hl r hla).trans ih

lemma achieve_adj_bound {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (hb : LinearIndependent ℝ b) (h : Achieve118 b k c)
    (hk : 2 ≤ k ∧ k ≤ n) :
    |mu c ⟨k-1,by omega⟩ ⟨k-2,by omega⟩| ≤ 1/2 := by
  unfold Achieve118 at h
  rw [dif_pos hk] at h
  rcases h with ⟨hbound,rfl⟩ | ⟨_,r,hr,rfl⟩
  · exact hbound
  · rw [mu_reduceBy_target hb (by change k-2 < k-1; omega) r]
    exact hr

lemma achieve_apply {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (h : Achieve118 b k c) {i : Fin n} (hi : i.val + 1 < k) : c i = b i := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨_,rfl⟩ | ⟨_,r,_,rfl⟩
    · rfl
    · exact reduceBy_apply_of_ne b r (by intro he; have := congrArg Fin.val he; dsimp at this; omega)
  · subst c; rfl

lemma loopStar_cond120 {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (hk : 2 ≤ k ∧ k ≤ n)
    (hb : |mu b ⟨k-1,by omega⟩ ⟨k-2,by omega⟩| ≤ 1/2)
    (hcond : Cond120 b k)
    (h : Relation.ReflTransGen (LoopStep (⟨k-1,by omega⟩ : Fin n)) b c) :
    Cond120 c k := by
  obtain ⟨_,hc⟩ := hcond
  refine ⟨hk,?_⟩
  rw [loopStar_gs h, loopStar_gs h, loopStar_top_mu (by change k-2+1 = k-1; omega) hb h]
  exact hc

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE LoopInvariants -/

/- BEGIN WHOLE MODULE SituationInvariant -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma gs_congr_below {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (h : ∀ i : Fin n, i.val + 1 < k → c i = b i) {i : Fin n}
    (hi : i.val + 1 < k) : gs c i = gs b i := by
  apply gs_congr_upto
  intro j hj
  exact h j (by omega)

lemma situation_of_prefix {n : ℕ} {b c : Fin n → Vec n} {k : ℕ}
    (hb : Situation b k) (h : ∀ i : Fin n, i.val + 1 < k → c i = b i) :
    Situation c k := by
  constructor
  · intro i j hji hik
    have hjk : j.val + 1 < k := by omega
    simpa only [mu, h i hik, gs_congr_below h hjk] using hb.1 i j hji hik
  · intro i hi hik hin
    obtain ⟨hk,hcond⟩ := hb.2 i hi hik hin
    refine ⟨hk,?_⟩
    have hia : (⟨i-1,by omega⟩ : Fin n).val + 1 < k := by dsimp; omega
    have hib : (⟨i-2,by omega⟩ : Fin n).val + 1 < k := by dsimp; omega
    simp only [mu, h _ hia, gs_congr_below h hia, gs_congr_below h hib]
    exact hcond

lemma situation_mono {n : ℕ} {b : Fin n → Vec n} {k l : ℕ}
    (h : Situation b k) (hl : l ≤ k) : Situation b l := by
  exact ⟨fun i j hji hi => h.1 i j hji (lt_of_lt_of_le hi hl),
    fun i hi hil hin => h.2 i hi (lt_of_lt_of_le hil hl) hin⟩

lemma situation_extend {n : ℕ} {b : Fin n → Vec n} {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ n) (h : Situation b k)
    (hrow : ∀ j : Fin n, j.val < k-1 → |mu b ⟨k-1,by omega⟩ j| ≤ 1/2)
    (hcond : k = 1 ∨ Cond120 b k) : Situation b (k+1) := by
  constructor
  · intro i j hji hik
    by_cases hi : i.val + 1 < k
    · exact h.1 i j hji hi
    · have heq : i = ⟨k-1,by omega⟩ := by apply Fin.ext; dsimp; omega
      rw [heq]
      apply hrow
      have := congrArg Fin.val heq
      dsimp at this
      omega
  · intro i hi hik hin
    by_cases hik' : i < k
    · exact h.2 i hi hik' hin
    · have heq : i = k := by omega
      subst i
      rcases hcond with hbad | hc
      · omega
      · exact hc

lemma step_situation {n : ℕ} {s t : State n} (hb : LinearIndependent ℝ s.1)
    (hs : Situation s.1 s.2) (h : Step s t) :
    Situation t.1 t.2 ∧ 1 ≤ t.2 ∧ t.2 ≤ n+1 := by
  rcases h with h | h
  · obtain ⟨hk,c,hc,_,ht,hk'⟩ := h
    have hs' : Situation c s.2 := situation_of_prefix hs (fun _ hi => achieve_apply hc hi)
    rw [ht,hk']
    refine ⟨?_,by omega,by omega⟩
    apply situation_of_prefix (situation_mono hs' (by omega))
    intro i hi
    simp only [Function.comp_apply]
    apply congrArg c
    apply Equiv.swap_apply_of_ne_of_ne <;> intro heq <;> subst i <;> dsimp at hi <;> omega
  · obtain ⟨hk,c,hc,hcond,hloop,hrow,hk'⟩ := h
    have hs' : Situation c s.2 := situation_of_prefix hs (fun _ hi => achieve_apply hc hi)
    have hs'' : Situation t.1 s.2 := situation_of_prefix hs' (fun i hi => loopStar_apply hloop (by intro he; have := congrArg Fin.val he; dsimp at this; omega))
    have hcond' : s.2 = 1 ∨ Cond120 t.1 s.2 := by
      rcases hcond with h1 | hcond
      · exact Or.inl h1
      · have hk2 : 2 ≤ s.2 ∧ s.2 ≤ n := hcond.1
        exact Or.inr (loopStar_cond120 hk2 (achieve_adj_bound hb hc hk2) hcond hloop)
    rw [hk']
    exact ⟨situation_extend hk hs'' hrow hcond',by omega,by omega⟩

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE SituationInvariant -/

/- BEGIN WHOLE MODULE AlgorithmProgress -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis

lemma step_exists {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
    {k : ℕ} (hk : 1 ≤ k ∧ k ≤ n) : ∃ t : State n, Step (b,k) t := by
  obtain ⟨c,hc⟩ := achieve_exists b k
  have hcb := (achieve_basis hb hc).1
  by_cases h119 : Cond119 c k
  · have hk2 := h119.1
    refine ⟨(c ∘ Equiv.swap (⟨k-2,by omega⟩ : Fin n) ⟨k-1,by omega⟩,k-1),Or.inl ?_⟩
    exact ⟨hk2,c,hc,h119,rfl,rfl⟩
  · have hcond : k = 1 ∨ Cond120 c k := by
      by_cases h1 : k = 1
      · exact Or.inl h1
      · have hk2 : 2 ≤ k ∧ k ≤ n := by omega
        refine Or.inr ⟨hk2,?_⟩
        apply le_of_not_gt
        intro hh
        exact h119 ⟨hk2,hh⟩
    obtain ⟨d,hloop,hrow⟩ := loop_complete hcb (⟨k-1,by omega⟩ : Fin n)
    refine ⟨(d,k+1),Or.inr ?_⟩
    exact ⟨hk,c,hc,hcond,hloop,hrow,rfl⟩

lemma situation_initial {n : ℕ} (b : Fin n → Vec n) : Situation b 2 := by
  constructor
  · intro i j hji hi; omega
  · intro i hi hik _; omega

lemma situation_final {n : ℕ} {b : Fin n → Vec n} (h : Situation b (n+1)) :
    IsReduced b := by
  constructor
  · intro i j hji
    exact h.1 i j hji (by omega)
  · intro i hi
    obtain ⟨_,hh⟩ := h.2 (i+2) (by omega) (by omega) (by omega)
    simpa using hh

lemma reachable_situation {n : ℕ} (hn : 0 < n) {b : Fin n → Vec n}
    (hb : LinearIndependent ℝ b) {s : State n} (h : Reachable b s) :
    Situation s.1 s.2 ∧ 1 ≤ s.2 ∧ s.2 ≤ n+1 := by
  induction h with
  | refl => exact ⟨situation_initial b,by omega,by omega⟩
  | @tail s t hst hstep ih => exact step_situation (reachable_basis hb hst).1 ih.1 hstep

lemma reachable_progress {n : ℕ} (hn : 0 < n) {b : Fin n → Vec n}
    (hb : LinearIndependent ℝ b) {s : State n} (h : Reachable b s) (hk : s.2 ≤ n) :
    ∃ t, Step s t := by
  exact step_exists (reachable_basis hb h).1 ⟨(reachable_situation hn hb h).2.1,hk⟩

lemma reachable_output {n : ℕ} (hn : 0 < n) {b : Fin n → Vec n}
    (hb : LinearIndependent ℝ b) {s : State n} (h : Reachable b s) (hk : s.2 = n+1) :
    IsBasisFor s.1 (latticeOf b) ∧ IsReduced s.1 := by
  refine ⟨reachable_basis hb h,?_⟩
  apply situation_final
  simpa only [hk] using (reachable_situation hn hb h).1

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE AlgorithmProgress -/

/- BEGIN WHOLE MODULE WeightedTermination -/
section
namespace LLLFactor.Reduction.Proof
open LLLFactor.RedBasis Filter

noncomputable def weightedPotential {n : ℕ} (s : State n) : ℝ :=
  potD s.1 * (7/6:ℝ) ^ (n+1-s.2)

lemma weightedPotential_ge {n : ℕ} (s : State n) (hs : LinearIndependent ℝ s.1) :
    potD s.1 ≤ weightedPotential s := by
  exact le_mul_of_one_le_right (potD_pos s.1 hs).le
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 7/6))

lemma weightedPotential_step {n : ℕ} {s t : State n}
    (hs : LinearIndependent ℝ s.1) (h : Step s t) :
    weightedPotential t ≤ (7/8:ℝ)*weightedPotential s := by
  rcases h with h | h
  · have hd := (case1_potential hs h).le
    obtain ⟨hk,c,hc,hcond,ht,hk'⟩ := h
    have he : n+1-t.2 = (n+1-s.2)+1 := by omega
    unfold weightedPotential
    rw [he, pow_succ]
    have hp : 0 ≤ (7/6:ℝ)^(n+1-s.2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hd hp]
  · have hd := case2_potential h
    obtain ⟨hk,c,hc,hcond,hloop,hrow,hk'⟩ := h
    have he : n+1-s.2 = (n+1-t.2)+1 := by omega
    unfold weightedPotential
    rw [hd, he, pow_succ]
    have hp : 0 ≤ potD s.1 * (7/6:ℝ)^(n+1-t.2) :=
      mul_nonneg (potD_pos s.1 hs).le (by positivity)
    nlinarith

lemma no_infinite_run {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b) :
    ¬ ∃ s : ℕ → State n, s 0 = (b,2) ∧ ∀ t, Step (s t) (s (t+1)) := by
  rintro ⟨s,hs0,hstep⟩
  have hr (t : ℕ) : Reachable b (s t) := by
    induction t with
    | zero => rw [hs0]; exact Relation.ReflTransGen.refl
    | succ t ih => exact ih.tail (hstep t)
  obtain ⟨d,hd,hbound⟩ := potential_uniform_lower_bound b hb
  have hlo (t : ℕ) : d ≤ weightedPotential (s t) :=
    (hbound (s t).1 (reachable_basis hb (hr t)).1 (reachable_basis hb (hr t)).2).trans
      (weightedPotential_ge _ (reachable_basis hb (hr t)).1)
  have hup (t : ℕ) : weightedPotential (s t) ≤ (7/8:ℝ)^t * weightedPotential (s 0) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hh := weightedPotential_step (reachable_basis hb (hr t)).1 (hstep t)
      calc
        _ ≤ (7/8:ℝ)*weightedPotential (s t) := hh
        _ ≤ (7/8:ℝ)*((7/8:ℝ)^t*weightedPotential (s 0)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have ht : Tendsto (fun t : ℕ => (7/8:ℝ)^t * weightedPotential (s 0)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 7/8)
      (by norm_num : (7/8:ℝ) < 1)).mul_const (weightedPotential (s 0))
  have hz : d ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall fun t => (hlo t).trans (hup t))
  linarith

end LLLFactor.Reduction.Proof
end
/- END WHOLE MODULE WeightedTermination -/

/- BEGIN WHOLE MODULE LLLRoot -/
section
namespace LLLFactor.Reduction

theorem algorithm_terminates {n : ℕ} (hn : 0 < n) (b : Fin n → LLLFactor.RedBasis.Vec n)
    (hb : LinearIndependent ℝ b) :
    (¬ ∃ s : ℕ → State n, s 0 = (b, 2) ∧ ∀ t, Step (s t) (s (t + 1))) ∧
    (∀ s : State n, Reachable b s → s.2 ≤ n → ∃ s' : State n, Step s s') ∧
    (∀ s : State n, Reachable b s → s.2 = n + 1 →
      LLLFactor.RedBasis.IsBasisFor s.1 (LLLFactor.RedBasis.latticeOf b) ∧ LLLFactor.RedBasis.IsReduced s.1) := by
  refine ⟨Proof.no_infinite_run b hb, ?_, ?_⟩
  · intro s hs hk
    exact Proof.reachable_progress hn hb hs hk
  · intro s hs hk
    exact Proof.reachable_output hn hb hs hk

end LLLFactor.Reduction
open LLLFactor.Reduction

theorem solution {n : ℕ} (hn : 0 < n) (b : Fin n → LLLFactor.RedBasis.Vec n)
    (hb : LinearIndependent ℝ b) :
    (¬ ∃ s : ℕ → State n, s 0 = (b, 2) ∧ ∀ t, Step (s t) (s (t + 1))) ∧
    (∀ s : State n, Reachable b s → s.2 ≤ n → ∃ s' : State n, Step s s') ∧
    (∀ s : State n, Reachable b s → s.2 = n + 1 →
      LLLFactor.RedBasis.IsBasisFor s.1 (LLLFactor.RedBasis.latticeOf b) ∧ LLLFactor.RedBasis.IsReduced s.1) := by
  exact LLLFactor.Reduction.algorithm_terminates hn b hb
end
/- END WHOLE MODULE LLLRoot -/

