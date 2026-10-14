-- Prove2me | solution 1 for IntMul.HvdH.thm_4_1
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:40:33.785988+00:00
-- url     : https://prove2.me/submissions/1a22d61e-8a53-49df-9b1a-109ffdc27435

import Theorems.Thm_IntMul_HvdH_prop_4_7_i

open Finset

namespace IntMul.HvdH.Tens

variable {d : ℕ}

/-- The tensor product of the kernels `M i : ZMod (t i) → ZMod (s i) → ℂ`, acting on
functions on `∏ i, ZMod (s i)`. -/
noncomputable def tens {s t : Fin d → ℕ} [∀ i, NeZero (s i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (u : ((i : Fin d) → ZMod (s i)) → ℂ) :
    ((i : Fin d) → ZMod (t i)) → ℂ :=
  fun k => ∑ j, (∏ i, M i (k i) (j i)) * u j

lemma tens_comp {r s t : Fin d → ℕ} [∀ i, NeZero (r i)] [∀ i, NeZero (s i)]
    (N : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ)
    (M : (i : Fin d) → ZMod (s i) → ZMod (r i) → ℂ) (u : ((i : Fin d) → ZMod (r i)) → ℂ) :
    tens N (tens M u) = tens (fun i k j => ∑ m, N i k m * M i m j) u := by
  ext k
  simp only [tens, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.prod_sum (fun i m => N i (k i) m * M i m (j i)), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.prod_mul_distrib]; ring

lemma tens_smul {s t : Fin d → ℕ} [∀ i, NeZero (s i)] (c : ℂ)
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (u : ((i : Fin d) → ZMod (s i)) → ℂ) :
    tens (fun i k j => c * M i k j) u = c ^ d • tens M u := by
  ext k
  simp only [tens, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl (fun j _ => ?_); ring

lemma tens_add {s t : Fin d → ℕ} [∀ i, NeZero (s i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (u v : ((i : Fin d) → ZMod (s i)) → ℂ) :
    tens M (u + v) = tens M u + tens M v := by
  ext k; simp only [tens, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma tens_smul' {s t : Fin d → ℕ} [∀ i, NeZero (s i)] (c : ℂ)
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (u : ((i : Fin d) → ZMod (s i)) → ℂ) :
    tens M (c • u) = c • tens M u := by
  ext k; simp only [tens, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_); ring

/-- Row sums `≤ 1` in every factor give sup-norm contraction. -/
lemma norm_tens_le {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (hM : ∀ i k, ∑ j, ‖M i k j‖ ≤ 1)
    (u : ((i : Fin d) → ZMod (s i)) → ℂ) : ‖tens M u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun k => ?_)
  calc ‖tens M u k‖ ≤ ∑ j, ‖(∏ i, M i (k i) (j i)) * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j : (i : Fin d) → ZMod (s i), (∏ i, ‖M i (k i) (j i)‖) * ‖u‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (by positivity)
    _ = (∏ i, ∑ m, ‖M i (k i) m‖) * ‖u‖ := by
        rw [← Finset.sum_mul, Fintype.prod_sum (fun i m => ‖M i (k i) m‖)]
    _ ≤ 1 * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_one (fun i _ => by positivity) (fun i _ => hM i (k i))
    _ = ‖u‖ := one_mul _

/-- Kernel of a linear map between coordinate spaces. -/
lemma clm_kernel {a b : ℕ} [NeZero a] (L : (ZMod a → ℂ) →L[ℂ] (ZMod b → ℂ)) (u : ZMod a → ℂ)
    (k : ZMod b) : L u k = ∑ j, L (Pi.single j 1) k * u j := by
  conv_lhs => rw [pi_eq_sum_univ u]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e : (fun i' => if j = i' then (1 : ℂ) else 0) = Pi.single j 1 := by
    funext i'; simp [Pi.single_apply, eq_comm]
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm, e]

/-- Row sums of the kernel are bounded by the sup-norm operator norm. -/
lemma kernel_row_le {a b : ℕ} [NeZero a] [NeZero b] (L : (ZMod a → ℂ) →L[ℂ] (ZMod b → ℂ))
    (k : ZMod b) : ∑ j, ‖L (Pi.single j 1) k‖ ≤ ‖L‖ := by
  set m : ZMod a → ℂ := fun j => L (Pi.single j 1) k with hm
  set u : ZMod a → ℂ := fun j => if m j = 0 then 0 else (starRingEnd ℂ) (m j) / (‖m j‖ : ℂ)
  have hu : ‖u‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun j => ?_)
    simp only [u]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h)]
  have hLu : L u k = ((∑ j, ‖m j‖ : ℝ) : ℂ) := by
    rw [clm_kernel, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show m j * u j = _
    simp only [u]
    split_ifs with h
    · simp [h]
    · rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have : (‖m j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
      field_simp
      push_cast; ring
  have h1 : ∑ j, ‖m j‖ = ‖L u k‖ := by
    rw [hLu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))]
  calc ∑ j, ‖m j‖ = ‖L u k‖ := h1
    _ ≤ ‖L u‖ := norm_le_pi_norm (L u) k
    _ ≤ ‖L‖ * ‖u‖ := L.le_opNorm u
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = ‖L‖ := mul_one _

noncomputable def tensCLM {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) :
    (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ) :=
  LinearMap.toContinuousLinearMap ⟨⟨tens M, tens_add M⟩, fun c u => tens_smul' c M u⟩

@[simp] lemma tensCLM_apply {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (u) : tensCLM M u = tens M u := rfl

lemma norm_tensCLM_le {s t : Fin d → ℕ} [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (M : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ) (hM : ∀ i k, ∑ j, ‖M i k j‖ ≤ 1) :
    ‖tensCLM M‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    rw [one_mul, tensCLM_apply]; exact norm_tens_le M hM u)

/-- Kernel form of Proposition 4.7(i). -/
lemma kernel_identity {a b : ℕ} [NeZero a] [NeZero b] (c : ℂ)
    (A : (ZMod a → ℂ) →L[ℂ] (ZMod b → ℂ)) (B : (ZMod b → ℂ) →L[ℂ] (ZMod a → ℂ))
    (h : ∀ u, (a : ℂ)⁻¹ • ZMod.dft u = c • B ((b : ℂ)⁻¹ • ZMod.dft (A u)))
    (k j : ZMod a) :
    (a : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k)) = c * ∑ m, B (Pi.single m 1) k *
      ∑ l, ((b : ℂ)⁻¹ * ZMod.stdAddChar (-(l * m))) * A (Pi.single j 1) l := by
  have h1 := congrFun (h (Pi.single j 1)) k
  have hL : ((a : ℂ)⁻¹ • ZMod.dft (Pi.single j (1 : ℂ))) k =
      (a : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k)) := by
    simp [ZMod.dft_apply, Pi.single_apply]
  rw [hL] at h1
  rw [h1, Pi.smul_apply, smul_eq_mul, clm_kernel B]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, ZMod.dft_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_); ring

end IntMul.HvdH.Tens

open IntMul.HvdH.Tens in
/-- **Harvey–van der Hoeven, Theorem 4.1** (multidimensional Gaussian resampling). -/
theorem IntMul.HvdH.thm_4_1_proof {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (α : ℕ)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ (α : ℝ) ^ 2 * ((t i : ℝ) / s i - 1)) :
    ∃ (A : (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ))
      (B : (((i : Fin d) → ZMod (t i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ u k, (∏ i, (s i : ℂ))⁻¹ * ∑ j, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u j =
        (2 : ℂ) ^ (2 * d * α ^ 2) * B (fun k' => (∏ i, (t i : ℂ))⁻¹ *
          ∑ l, (∏ i, (ZMod.stdAddChar (-(l i * k' i)) : ℂ)) * A u l) k := by
  have h1 := fun i => IntMul.HvdH.prop_4_7_i (s i) (t i) α (hst i) (hcop i) hα (hθ i)
  choose A B hA hB hAB using h1
  set a : (i : Fin d) → ZMod (t i) → ZMod (s i) → ℂ := fun i l j => A i (Pi.single j 1) l
  set b : (i : Fin d) → ZMod (s i) → ZMod (t i) → ℂ := fun i k m => B i (Pi.single m 1) k
  set ft : (i : Fin d) → ZMod (t i) → ZMod (t i) → ℂ :=
    fun i m l => (t i : ℂ)⁻¹ * ZMod.stdAddChar (-(l * m))
  set fs : (i : Fin d) → ZMod (s i) → ZMod (s i) → ℂ :=
    fun i k j => (s i : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k))
  have hdft : ∀ (r : Fin d → ℕ) [∀ i, NeZero (r i)] (u : ((i : Fin d) → ZMod (r i)) → ℂ) k,
      (∏ i, (r i : ℂ))⁻¹ * ∑ j, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u j =
        tens (fun i k j => (r i : ℂ)⁻¹ * ZMod.stdAddChar (-(j * k))) u k := by
    intro r _ u k
    simp only [tens, Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  have hker : fs = fun i k j => (2 : ℂ) ^ (2 * α ^ 2) * ∑ m, b i k m * ∑ l, ft i m l * a i l j := by
    funext i k j
    exact kernel_identity _ (A i) (B i) (hAB i) k j
  refine ⟨tensCLM a, tensCLM b, norm_tensCLM_le a (fun i l => (kernel_row_le (A i) l).trans (hA i)),
    norm_tensCLM_le b (fun i k => (kernel_row_le (B i) k).trans (hB i)), fun u k => ?_⟩
  rw [hdft s u k]
  have hR : (fun k' => (∏ i, (t i : ℂ))⁻¹ *
      ∑ l, (∏ i, (ZMod.stdAddChar (-(l i * k' i)) : ℂ)) * tensCLM a u l) = tens ft (tens a u) := by
    funext k'; rw [hdft t]; rfl
  rw [hR, tensCLM_apply, tens_comp, tens_comp]
  change tens fs u k = _
  rw [hker, tens_smul, Pi.smul_apply, smul_eq_mul, ← pow_mul,
    show 2 * α ^ 2 * d = 2 * d * α ^ 2 by ring]
  congr 2; funext i k j
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem solution {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (α : ℕ)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ (α : ℝ) ^ 2 * ((t i : ℝ) / s i - 1)) :
    ∃ (A : (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ))
      (B : (((i : Fin d) → ZMod (t i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ u k, (∏ i, (s i : ℂ))⁻¹ * ∑ j, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u j =
        (2 : ℂ) ^ (2 * d * α ^ 2) * B (fun k' => (∏ i, (t i : ℂ))⁻¹ *
          ∑ l, (∏ i, (ZMod.stdAddChar (-(l i * k' i)) : ℂ)) * A u l) k :=
  IntMul.HvdH.thm_4_1_proof s t α hst hcop hα hθ
