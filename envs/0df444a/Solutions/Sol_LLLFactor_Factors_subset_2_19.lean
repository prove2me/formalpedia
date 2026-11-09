-- Prove2me | solution 1 for LLLFactor.Factors.subset_2_19
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:59:37.993496+00:00
-- url     : https://prove2.me/submissions/ca51adfa-237d-4c8a-8f67-5e4335cba755

import Definitions.Def_LLLFactor_Factors_Setting
import Theorems.Thm_LLLFactor_Factors_mignotte_step
import Theorems.Thm_LLLFactor_Factors_prop_2_5

open Polynomial Finset InnerProductSpace Submodule LLLFactor.Factors

namespace Subset219Proof
noncomputable section

lemma polyNorm_nonneg (f : ℤ[X]) : 0 ≤ polyNorm f := Real.sqrt_nonneg _

lemma polyNorm_sq (f : ℤ[X]) :
    polyNorm f ^ 2 = ∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sum_coeff_sq_le (f : ℤ[X]) (s : Finset ℕ) :
    (∑ i ∈ s, (f.coeff i : ℝ) ^ 2) ≤ polyNorm f ^ 2 := by
  rw [polyNorm_sq]
  calc
    _ ≤ ∑ i ∈ f.support ∪ s, (f.coeff i : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by intros; positivity)
    _ = _ := (Finset.sum_subset Finset.subset_union_left (by
      intro i _ hi
      simp [Polynomial.notMem_support_iff.mp hi])).symm

lemma one_le_polyNorm {f : ℤ[X]} (hf : f ≠ 0) : 1 ≤ polyNorm f := by
  have hc : (1 : ℝ) ≤ |(f.leadingCoeff : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hf))
  have hs := sum_coeff_sq_le f {f.natDegree}
  simp only [Finset.sum_singleton, coeff_natDegree] at hs
  have hn := polyNorm_nonneg f
  nlinarith [sq_abs (f.leadingCoeff : ℝ)]

lemma polyNorm_pos {f : ℤ[X]} (hf : f ≠ 0) : 0 < polyNorm f :=
  lt_of_lt_of_le zero_lt_one (one_le_polyNorm hf)

lemma norm_coeffVec_eq (m : ℕ) (f : ℤ[X]) (hf : f.natDegree ≤ m) :
    ‖coeffVec m f‖ = polyNorm f := by
  apply (sq_eq_sq₀ (norm_nonneg _) (polyNorm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, polyNorm_sq]
  change (∑ i : Fin (m + 1), (f.coeff i : ℝ) ^ 2) = _
  rw [show (∑ i : Fin (m + 1), (f.coeff i : ℝ) ^ 2) =
      ∑ i ∈ Finset.range (m + 1), (f.coeff i : ℝ) ^ 2 from
      Fin.sum_univ_eq_sum_range (fun i => (f.coeff i : ℝ) ^ 2) (m + 1)]
  exact (f.sum_over_range' (f := fun _ a => (a : ℝ) ^ 2) (by simp) (m + 1)
    (by omega)).symm

lemma polyNorm_X_pow_mul (f : ℤ[X]) (k : ℕ) : polyNorm (X ^ k * f) = polyNorm f := by
  have hs : (X ^ k * f).support = f.support.image (fun i => i + k) := by
    ext i
    constructor
    · intro hi
      have hn := Polynomial.mem_support_iff.mp hi
      rw [Polynomial.coeff_X_pow_mul'] at hn
      have hk : k ≤ i := by by_contra h; simp [h] at hn
      rw [if_pos hk] at hn
      exact Finset.mem_image.mpr ⟨i - k, Polynomial.mem_support_iff.mpr hn, by omega⟩
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      simpa only [Polynomial.mem_support_iff, Polynomial.coeff_X_pow_mul] using hj
  unfold polyNorm
  rw [hs, Finset.sum_image]
  · simp only [Polynomial.coeff_X_pow_mul]
  · intro i _ j _ hij
    exact Nat.add_right_cancel hij

lemma coeffVec_sum_zsmul {ι : Type*} [Fintype ι] (m : ℕ) (b : ι → ℤ[X]) (z : ι → ℤ) :
    coeffVec m (∑ i, z i • b i) = ∑ i, (z i : ℝ) • coeffVec m (b i) := by
  ext j
  simp [coeffVec, zsmul_eq_mul]

lemma coeffVec_integer_expansion {ι : Type*} [Fintype ι] (m : ℕ) (b : ι → ℤ[X])
    (f : ℤ[X]) (hf : f ∈ Submodule.span ℤ (Set.range b)) :
    ∃ z : ι → ℤ, ∑ i, (z i : ℝ) • coeffVec m (b i) = coeffVec m f := by
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hf
  refine ⟨z, ?_⟩
  rw [← coeffVec_sum_zsmul, hz]

lemma norm_sq_sum_orthogonal {N : ℕ} {ι : Type*} [DecidableEq ι]
    (x : ι → EuclideanSpace ℝ (Fin N)) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (x i) (x j) = 0) :
    ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, norm_add_sq_real]
    have hz : inner ℝ (x a) (∑ i ∈ s, x i) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact h a (mem_insert_self _ _) i (mem_insert_of_mem hi) (by intro he; subst i; exact ha hi)
    rw [hz, mul_zero, add_zero, ih (fun i hi j hj hij =>
      h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)]

lemma gs_expansion {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    v i = gs v i + ∑ j ∈ Iio i, mu v i j • gs v j := by
  simpa only [gs, mu, real_inner_comm, real_inner_self_eq_norm_sq, RCLike.ofReal_real_eq_id, id_eq]
    using gramSchmidt_def'' ℝ v i

lemma gs_orthogonal {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N))
    {i j : Fin N} (h : i ≠ j) : inner ℝ (gs v i) (gs v j) = 0 :=
  gramSchmidt_orthogonal ℝ v h

lemma reduced_mu_sq {N : ℕ} {v : Fin N → EuclideanSpace ℝ (Fin N)}
    (hv : IsReduced v) {i j : Fin N} (hji : j < i) : (mu v i j) ^ 2 ≤ (1 / 4 : ℝ) := by
  have h := (sq_le_sq₀ (abs_nonneg (mu v i j)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr (hv.1 i j hji)
  norm_num [sq_abs] at h ⊢
  exact h

lemma reduced_gs_step {N : ℕ} {v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1))}
    (hv : IsReduced v) (i : Fin N) : ‖gs v i.castSucc‖ ^ 2 ≤ 2 * ‖gs v i.succ‖ ^ 2 := by
  have h := hv.2 i.val (by omega)
  change (3 / 4 : ℝ) * ‖gs v i.castSucc‖ ^ 2 ≤
    ‖gs v i.succ + mu v i.succ i.castSucc • gs v i.castSucc‖ ^ 2 at h
  rw [norm_add_sq_real, inner_smul_right,
    gs_orthogonal v (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne', mul_zero,
    mul_zero, add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have hm := mul_le_mul_of_nonneg_right
    (reduced_mu_sq hv (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
    (sq_nonneg ‖gs v i.castSucc‖)
  nlinarith

lemma reduced_scaled_gs_mono {N : ℕ} {v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1))}
    (hv : IsReduced v) : Monotone (fun i : Fin (N + 1) => (2 : ℝ) ^ i.val * ‖gs v i‖ ^ 2) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := mul_le_mul_of_nonneg_left (reduced_gs_step hv i) (by positivity : (0 : ℝ) ≤ 2 ^ i.val)
  simpa only [Fin.val_castSucc, Fin.val_succ, pow_succ, mul_assoc] using h

lemma reduced_prefix_gs_bound {N : ℕ} {v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1))}
    (hv : IsReduced v) (j : Fin (N + 1)) :
    (∑ i ∈ Iio j, ‖gs v i‖ ^ 2) ≤ ((2 : ℝ) ^ (j.val + 1) - 2) * ‖gs v j‖ ^ 2 := by
  induction j using Fin.induction with
  | zero =>
    rw [show Iio (0 : Fin (N + 1)) = ∅ by ext i; simp]
    simp
  | @succ j ih =>
    have he : Iio j.succ = insert j.castSucc (Iio j.castSucc) := by
      ext i
      simp only [mem_Iio, mem_insert, Fin.lt_def, Fin.val_succ,
        Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [he, Finset.sum_insert (by simp)]
    have hs := reduced_gs_step hv j
    have hp : (0 : ℝ) ≤ 2 ^ (j.val + 1) - 1 := by
      have h : (1 : ℝ) ≤ 2 ^ (j.val + 1) := one_le_pow₀ (by norm_num)
      linarith
    have hh := mul_le_mul_of_nonneg_left hs hp
    simp only [Fin.val_castSucc] at ih
    simp only [Fin.val_succ, pow_succ] at *
    nlinarith

lemma reduced_vector_sq_bound {N : ℕ} {v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1))}
    (hv : IsReduced v) (j : Fin (N + 1)) : ‖v j‖ ^ 2 ≤ (2 : ℝ) ^ j.val * ‖gs v j‖ ^ 2 := by
  have he : ‖v j‖ ^ 2 = ‖gs v j‖ ^ 2 + ∑ i ∈ Iio j, (mu v j i) ^ 2 * ‖gs v i‖ ^ 2 := by
    conv_lhs => rw [gs_expansion v j]
    rw [norm_add_sq_real]
    have hz : inner ℝ (gs v j) (∑ i ∈ Iio j, mu v j i • gs v i) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [inner_smul_right, gs_orthogonal v (by have := mem_Iio.mp hi; omega), mul_zero]
    rw [hz, mul_zero, add_zero, norm_sq_sum_orthogonal]
    · simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    · intro i _ k _ hik
      simp only [inner_smul_left, inner_smul_right, gs_orthogonal v hik, mul_zero,
        RCLike.conj_to_real]
  have hb : (∑ i ∈ Iio j, (mu v j i) ^ 2 * ‖gs v i‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ i ∈ Iio j, ‖gs v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (reduced_mu_sq hv (mem_Iio.mp hi)) (sq_nonneg _)
  have hp := reduced_prefix_gs_bound hv j
  have htwo : (1 : ℝ) ≤ 2 ^ j.val := one_le_pow₀ (by norm_num)
  have hh := mul_nonneg (sub_nonneg.mpr htwo) (sq_nonneg ‖gs v j‖)
  rw [pow_succ] at hp
  nlinarith

lemma reduced_vector_gs_bound {N : ℕ} {v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1))}
    (hv : IsReduced v) {j r : Fin (N + 1)} (hjr : j ≤ r) :
    ‖v j‖ ^ 2 ≤ (2 : ℝ) ^ r.val * ‖gs v r‖ ^ 2 :=
  (reduced_vector_sq_bound hv j).trans (reduced_scaled_gs_mono hv hjr)

lemma independent_outside_prefix {N d : ℕ}
    (v : Fin N → EuclideanSpace ℝ (Fin N)) (x : Fin d → EuclideanSpace ℝ (Fin N))
    (hx : LinearIndependent ℝ x) (j : ℕ) (hjN : j ≤ N) (hjd : j < d) :
    ∃ i, x i ∉ Submodule.span ℝ (Set.range (fun a : Fin j => v ⟨a.val, lt_of_lt_of_le a.isLt hjN⟩)) := by
  classical
  by_contra h
  push Not at h
  let W := Submodule.span ℝ (Set.range (fun a : Fin j => v ⟨a.val, lt_of_lt_of_le a.isLt hjN⟩))
  let y : Fin d → W := fun i => ⟨x i, h i⟩
  have hy : LinearIndependent ℝ y := LinearIndependent.of_comp W.subtype hx
  have hd := hy.fintype_card_le_finrank
  have hj := finrank_range_le_card (R := ℝ) (fun a : Fin j => v ⟨a.val, lt_of_lt_of_le a.isLt hjN⟩)
  simp only [Fintype.card_fin] at hd hj
  change Module.finrank ℝ W ≤ j at hj
  omega

lemma inner_gs_vector_self {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) (r : Fin N) :
    inner ℝ (gs v r) (v r) = ‖gs v r‖ ^ 2 := by
  rw [gs_expansion v r, inner_add_right, inner_sum]
  have h : (∑ i ∈ Iio r, inner ℝ (gs v r) (mu v r i • gs v i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [inner_smul_right, gs_orthogonal v (by have := mem_Iio.mp hi; omega), mul_zero]
  rw [h, add_zero, real_inner_self_eq_norm_sq]

lemma integral_top_index {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (z : Fin N → ℤ)
    (hx : ∑ i, (z i : ℝ) • v i = x) (j : ℕ) (hj : j ≤ N)
    (hout : x ∉ Submodule.span ℝ (Set.range (fun a : Fin j => v ⟨a.val, lt_of_lt_of_le a.isLt hj⟩))) :
    ∃ r : Fin N, j ≤ r.val ∧ z r ≠ 0 ∧ ∀ i, r < i → z i = 0 := by
  classical
  let s := Finset.univ.filter (fun i => z i ≠ 0)
  have hs : s.Nonempty := by
    by_contra h
    have hz : ∀ i, z i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, by simp [s, hi]⟩
    apply hout
    rw [← hx]
    simp [hz]
  let r := s.max' hs
  have hr : z r ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have ht : ∀ i, r < i → z i = 0 := by
    intro i hi
    by_contra hz
    have hm : i ∈ s := by simp [s, hz]
    have := Finset.le_max' s i hm
    exact (not_le_of_gt hi) this
  refine ⟨r, ?_, hr, ht⟩
  by_contra h
  apply hout
  rw [← hx]
  apply Submodule.sum_mem
  intro i _
  by_cases hij : i.val < j
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i.val, hij⟩, rfl⟩
  · have hz : z i = 0 := ht i (by omega)
    simp [hz]

lemma integral_top_norm {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N))
    (hv : LinearIndependent ℝ v) (x : EuclideanSpace ℝ (Fin N)) (z : Fin N → ℤ)
    (hx : ∑ i, (z i : ℝ) • v i = x) (r : Fin N) (hr : z r ≠ 0)
    (ht : ∀ i, r < i → z i = 0) : ‖gs v r‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have he : inner ℝ (gs v r) x = (z r : ℝ) * ‖gs v r‖ ^ 2 := by
    rw [← hx, inner_sum]
    rw [Finset.sum_eq_single r]
    · rw [inner_smul_right, inner_gs_vector_self]
    · intro i _ hir
      rcases lt_or_gt_of_ne hir with hi | hi
      · rw [inner_smul_right]
        have hh : inner ℝ (gs v r) (v i) = 0 := gramSchmidt_inv_triangular ℝ v hi
        rw [hh, mul_zero]
      · simp [ht i hi]
    · simp
  have hc := abs_real_inner_le_norm (gs v r) x
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg ‖gs v r‖)] at hc
  have hz : (1 : ℝ) ≤ |(z r : ℝ)| := by exact_mod_cast Int.one_le_abs hr
  have hl := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖gs v r‖)
  have hp : 0 < ‖gs v r‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero r hv)
  have hn := norm_nonneg x
  have hnorm : ‖gs v r‖ ≤ ‖x‖ := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hn).mpr hnorm

lemma reduced_independent_bound {N d : ℕ}
    (v : Fin (N + 1) → EuclideanSpace ℝ (Fin (N + 1)))
    (hv : LinearIndependent ℝ v) (hred : IsReduced v)
    (x : Fin d → EuclideanSpace ℝ (Fin (N + 1))) (hx : LinearIndependent ℝ x)
    (hrep : ∀ i, ∃ z : Fin (N + 1) → ℤ, ∑ a, (z a : ℝ) • v a = x i)
    (B : ℝ) (hB : ∀ i, ‖x i‖ ^ 2 ≤ B)
    (j : Fin (N + 1)) (hj : j.val < d) : ‖v j‖ ^ 2 ≤ (2 : ℝ) ^ N * B := by
  obtain ⟨i, hi⟩ := independent_outside_prefix v x hx j.val (by omega) hj
  obtain ⟨z, hz⟩ := hrep i
  obtain ⟨r, hrj, hr, hrt⟩ := integral_top_index v (x i) z hz j.val (by omega) hi
  have ht := integral_top_norm v hv (x i) z hz r hr hrt
  calc
    ‖v j‖ ^ 2 ≤ (2 : ℝ) ^ r.val * ‖gs v r‖ ^ 2 := reduced_vector_gs_bound hred (by omega)
    _ ≤ (2 : ℝ) ^ N * ‖gs v r‖ ^ 2 := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : r.val ≤ N)) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (ht.trans (hB i)) (by positivity)

lemma shifts_independent {m d : ℕ} (h : ℤ[X]) (hh : h ≠ 0)
    (hd : h.natDegree + d ≤ m + 1) :
    LinearIndependent ℝ (fun i : Fin d => coeffVec m (X ^ i.val * h)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  by_contra hi
  let s := Finset.univ.filter (fun j => a j ≠ 0)
  have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
  let r := s.max' hs
  have hr : a r ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have ht : ∀ j, r < j → a j = 0 := by
    intro j hj
    by_contra hz
    exact (not_le_of_gt hj) (Finset.le_max' s j (by simp [s, hz]))
  have hb : h.natDegree + r.val < m + 1 := by have := r.isLt; omega
  have he := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v ⟨h.natDegree + r.val, hb⟩) ha
  have he' : (∑ j : Fin d, a j * ((X ^ j.val * h).coeff (h.natDegree + r.val) : ℝ)) = 0 := by
    simpa [coeffVec] using he
  rw [Finset.sum_eq_single r] at he'
  · rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_natDegree] at he'
    have hl : (h.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hh
    exact hr (mul_eq_zero.mp he' |>.resolve_right hl)
  · intro j _ hjr
    rcases lt_or_gt_of_ne hjr with hj | hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · simp
      · rw [Polynomial.natDegree_X_pow_mul j.val hh]
        have : j.val < r.val := hj
        omega
    · simp [ht j hj]
  · simp

lemma threshold_pow (F P : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P) (hn : 0 < n) :
    ((P / F ^ m) ^ ((1 : ℝ) / (n : ℝ))) ^ n = P / F ^ m := by
  rw [← Real.rpow_mul_natCast (le_of_lt (div_pos hP (pow_pos hF _)))]
  rw [div_mul_cancel₀ (1 : ℝ) (by exact_mod_cast ne_of_gt hn), Real.rpow_one]

lemma threshold_iff (F P B : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P)
    (hB : 0 ≤ B) (hn : 0 < n) :
    B < (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) ↔ F ^ m * B ^ n < P := by
  have hp := threshold_pow F P m n hF hP hn
  have ht : 0 ≤ (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (div_pos hP (pow_pos hF _))) _
  have he := Real.rpow_lt_rpow_iff hB ht (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  rw [Real.rpow_natCast, Real.rpow_natCast, hp] at he
  rw [← he, lt_div_iff₀ (pow_pos hF _)]
  exact ⟨fun h => by simpa only [mul_comm] using h, fun h => by simpa only [mul_comm] using h⟩

lemma short_bound_from_sq (F C P B : ℝ) (m n : ℕ)
    (hF : 0 < F) (hC : 0 < C) (hP : 0 < P) (hB : 0 ≤ B) (hn : 0 < n)
    (hb : B ^ 2 ≤ (2 : ℝ) ^ m * C * F ^ 2)
    (hbig : (2 : ℝ) ^ ((m : ℝ) * (n : ℝ) / 2) * C ^ ((n : ℝ) / 2) * F ^ (m + n) < P) :
    B < (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) := by
  let A := (2 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt C * F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAsq : A ^ 2 = (2 : ℝ) ^ m * C * F ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hBA : B ≤ A := (sq_le_sq₀ hB hA).mp (hb.trans_eq hAsq.symm)
  have hAn : F ^ m * A ^ n = (2 : ℝ) ^ ((m : ℝ) * (n : ℝ) / 2) * C ^ ((n : ℝ) / 2) * F ^ (m + n) := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast hC.le]
    rw [show (m : ℝ) / 2 * (n : ℝ) = (m : ℝ) * (n : ℝ) / 2 by ring,
      show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring, pow_add]
    ring
  apply (threshold_iff F P B m n hF hP hB hn).mpr
  calc
    F ^ m * B ^ n ≤ F ^ m * A ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBA _) (by positivity)
    _ < P := by rw [hAn]; exact hbig

lemma h0_shift_mem {p k m : ℕ} {f h h0 : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0) (hd : h0.natDegree ≤ m)
    (i : Fin (m + 1 - h0.natDegree)) : X ^ i.val * h0 ∈ latticeL p k h m := by
  refine ⟨?_, ?_⟩
  · rw [Polynomial.natDegree_X_pow_mul i.val hh0.1.ne_zero]
    have := i.isLt
    omega
  · simp only [modPk, Polynomial.map_mul]
    exact dvd_mul_of_dvd_right ((prop_2_5 f h hS).2.2.2 h0 hh0) _

lemma native_prefix_sq_bound {p k m : ℕ} {f h h0 : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0) (hd : h0.natDegree ≤ m)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (j : Fin (m + 1)) (hj : j.val < m + 1 - h0.natDegree) :
    polyNorm (b j) ^ 2 ≤ (2 : ℝ) ^ m * polyNorm h0 ^ 2 := by
  let x : Fin (m + 1 - h0.natDegree) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun i => coeffVec m (X ^ i.val * h0)
  have hx : LinearIndependent ℝ x := shifts_independent h0 hh0.1.ne_zero (by omega)
  have hrep : ∀ i, ∃ z : Fin (m + 1) → ℤ,
      ∑ a, (z a : ℝ) • (coeffVec m ∘ b) a = x i := by
    intro i
    exact coeffVec_integer_expansion m b _ (hb.2.2.1 _ (h0_shift_mem hS hh0 hd i))
  have hnorm : ∀ i, ‖x i‖ ^ 2 ≤ polyNorm h0 ^ 2 := by
    intro i
    dsimp [x]
    rw [norm_coeffVec_eq m _ (h0_shift_mem hS hh0 hd i).1, polyNorm_X_pow_mul]
  have he := reduced_independent_bound (coeffVec m ∘ b) hb.2.1 hb.2.2.2 x hx hrep
    (polyNorm h0 ^ 2) hnorm j hj
  simpa only [Function.comp_apply, norm_coeffVec_eq m _ (hb.1 j).1] using he

end
end Subset219Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (_hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree))
    (hdeg : h₀.natDegree ≤ m) :
    ∀ j : Fin (m + 1), (j : ℕ) < m + 1 - h₀.natDegree →
      polyNorm (b j) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)) := by
  intro j hj
  have hf : f ≠ 0 := by
    intro hz
    have h := hS.deg_f_pos
    simp [hz] at h
  have hp : (0 : ℝ) < p := by exact_mod_cast hS.prime.pos
  have hc : (0 : ℝ) < ((2 * m).choose m : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  apply Subset219Proof.short_bound_from_sq (polyNorm f) ((2 * m).choose m : ℝ)
    ((p : ℝ) ^ (k * h.natDegree)) (polyNorm (b j)) m f.natDegree
    (Subset219Proof.polyNorm_pos hf) hc (pow_pos hp _) (Subset219Proof.polyNorm_nonneg _)
    hS.deg_f_pos ?_ h214
  have h1 := Subset219Proof.native_prefix_sq_bound hS hh₀ hdeg b hb j hj
  have hmig := mignotte_step f hf m h₀ hh₀.2.1 hdeg
  rw [← Real.sqrt_eq_rpow] at hmig
  have hmig_sq : polyNorm h₀ ^ 2 ≤ ((2 * m).choose m : ℝ) * polyNorm f ^ 2 := by
    have hsq := (sq_le_sq₀ (Subset219Proof.polyNorm_nonneg h₀)
      (mul_nonneg (Real.sqrt_nonneg _) (Subset219Proof.polyNorm_nonneg f))).mpr hmig
    rw [mul_pow, Real.sq_sqrt hc.le] at hsq
    exact hsq
  have h2 := mul_le_mul_of_nonneg_left hmig_sq (by positivity : (0 : ℝ) ≤ 2 ^ m)
  exact h1.trans (by simpa only [mul_assoc] using h2)
