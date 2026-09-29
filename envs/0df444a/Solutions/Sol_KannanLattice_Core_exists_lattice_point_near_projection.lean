-- Prove2me | solution 1 for KannanLattice.Core.exists_lattice_point_near_projection
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:15:28.813203+00:00
-- url     : https://prove2.me/submissions/974f9d1c-8df0-4c91-b31d-8f1aaa8986a8

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice



namespace KannanLattice.Core

open InnerProductSpace

lemma lattice_le_span {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    {v : EuclideanSpace ℝ (Fin k)} (hv : v ∈ lattice b) :
    v ∈ Submodule.span ℝ (Set.range b) := by
  unfold lattice at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hx

lemma inner_gsN_lt {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) {t j : Fin m}
    (h : t < j) : inner ℝ (gramSchmidtNormed ℝ b j) (b t) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular ℝ b h]

lemma inner_gs_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidt ℝ b t) (b t) = ‖gramSchmidt ℝ b t‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ b t]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.1 hi).ne', mul_zero]

lemma inner_gsN_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidtNormed ℝ b t) (b t) = gsLen b t := by
  unfold gramSchmidtNormed gsLen
  rw [inner_smul_left, inner_gs_self]
  simp only [RCLike.conj_to_real]
  by_cases h : ‖gramSchmidt ℝ b t‖ = 0
  · simp [h]
  · field_simp
    rfl

lemma gsLen_pos {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (t : Fin m) : 0 < gsLen b t := by
  unfold gsLen
  exact norm_pos_iff.2 (gramSchmidt_ne_zero t hb)

lemma norm_sq_eq_sum_inner {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (w : EuclideanSpace ℝ (Fin k))
    (hw : w ∈ Submodule.span ℝ (Set.range b)) :
    ‖w‖ ^ 2 = ∑ j, (inner ℝ (gramSchmidtNormed ℝ b j) w) ^ 2 := by
  have hu := gramSchmidtNormed_orthonormal (𝕜 := ℝ) hb
  rw [← span_gramSchmidt ℝ b, ← span_gramSchmidtNormed_range] at hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
  have hc : ∀ j, inner ℝ (gramSchmidtNormed ℝ b j) (∑ i, a i • gramSchmidtNormed ℝ b i) = a j :=
    fun j => hu.inner_right_fintype a j
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, hc]
  simp [sq]

theorem near_core (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (b₀ : EuclideanSpace ℝ (Fin k)) :
    ∃ v ∈ lattice b,
      ‖v - (Submodule.span ℝ (Set.range b)).starProjection b₀‖ ≤
          (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) ∧
      ∀ i : Fin m, (∀ j : Fin m, gsLen b j ≤ gsLen b i) →
        ‖(Submodule.span ℝ (Set.range b)).starProjection b₀ - v‖ ≤
          Real.sqrt m / 2 * gsLen b i := by
  set S := Submodule.span ℝ (Set.range b) with hS
  set p := S.starProjection b₀ with hp
  set u := gramSchmidtNormed ℝ b with hu
  have key : ∀ s, s ≤ m → ∃ v ∈ lattice b, ∀ j : Fin m, m - s ≤ (j : ℕ) →
      |inner ℝ (u j) (v - p)| ≤ gsLen b j / 2 := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨0, Submodule.zero_mem _, fun j hj => ?_⟩
      exfalso; have := j.2; omega
    | succ s ih =>
      intro hs
      obtain ⟨v, hv, hvj⟩ := ih (by omega)
      set t : Fin m := ⟨m - s - 1, by omega⟩ with ht
      have hpos := gsLen_pos b hb t
      set x := inner ℝ (u t) (v - p) / gsLen b t with hx
      refine ⟨v - round x • b t, ?_, ?_⟩
      · exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
      · intro j hj
        have e : v - round x • b t - p = (v - p) - ((round x : ℤ) : ℝ) • b t := by
          rw [Int.cast_smul_eq_zsmul]; abel
        rw [e, inner_sub_right, inner_smul_right]
        rcases (show (j : ℕ) = m - s - 1 ∨ m - s ≤ (j : ℕ) by omega) with h1 | h1
        · have : j = t := Fin.ext h1
          subst this
          rw [hu, inner_gsN_self, ← hu]
          have h2 : inner ℝ (u t) (v - p) = x * gsLen b t := by
            rw [hx]; field_simp
          rw [h2, ← sub_mul, abs_mul, abs_of_pos hpos]
          have := abs_sub_round x
          nlinarith
        · have hlt : t < j := by
            rw [Fin.lt_def]; simp [ht]; omega
          rw [hu, inner_gsN_lt b hlt, ← hu, mul_zero, sub_zero]
          exact hvj j h1
  obtain ⟨v, hv, hvj⟩ := key m le_rfl
  have hvj' : ∀ j, |inner ℝ (u j) (v - p)| ≤ gsLen b j / 2 := fun j => hvj j (by omega)
  have hw : v - p ∈ S := Submodule.sub_mem _ (lattice_le_span b hv) (S.starProjection_apply_mem b₀)
  have hn := norm_sq_eq_sum_inner b hb (v - p) hw
  have hbound : ‖v - p‖ ^ 2 ≤ (1/4 : ℝ) * ∑ j, gsLen b j ^ 2 := by
    rw [hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hvj' j
    have h0 : 0 ≤ gsLen b j := (gsLen_pos b hb j).le
    have : (inner ℝ (u j) (v - p)) ^ 2 ≤ (gsLen b j / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith
  have hfirst : ‖v - p‖ ≤ (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) := by
    have : (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) =
        Real.sqrt ((1/4 : ℝ) * ∑ j, gsLen b j ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), show (1/4 : ℝ) = (1/2)^2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.le_sqrt_of_sq_le hbound
  refine ⟨v, hv, hfirst, fun i hi => ?_⟩
  rw [norm_sub_rev]
  refine hfirst.trans ?_
  have h0 : 0 ≤ gsLen b i := (gsLen_pos b hb i).le
  have hsum : ∑ j, gsLen b j ^ 2 ≤ (m : ℝ) * gsLen b i ^ 2 := by
    calc ∑ j, gsLen b j ^ 2 ≤ ∑ _j : Fin m, gsLen b i ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (gsLen_pos b hb j).le (hi j) 2
      _ = (m : ℝ) * gsLen b i ^ 2 := by simp
  have : Real.sqrt (∑ j, gsLen b j ^ 2) ≤ Real.sqrt m * gsLen b i := by
    calc Real.sqrt (∑ j, gsLen b j ^ 2) ≤ Real.sqrt ((m : ℝ) * gsLen b i ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * gsLen b i := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0]
  linarith

end KannanLattice.Core

open KannanLattice.Core


theorem solution (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (b₀ : EuclideanSpace ℝ (Fin k)) :
    ∃ v ∈ lattice b,
      ‖v - (Submodule.span ℝ (Set.range b)).starProjection b₀‖ ≤
          (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) ∧
      ∀ i : Fin m, (∀ j : Fin m, gsLen b j ≤ gsLen b i) →
        ‖(Submodule.span ℝ (Set.range b)).starProjection b₀ - v‖ ≤
          Real.sqrt m / 2 * gsLen b i := by
  exact near_core m k b hb b₀
