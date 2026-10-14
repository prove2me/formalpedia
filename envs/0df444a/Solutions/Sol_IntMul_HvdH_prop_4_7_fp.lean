-- Prove2me | solution 1 for IntMul.HvdH.prop_4_7_fp
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T01:09:20.650617+00:00
-- url     : https://prove2.me/submissions/3785c1f6-1881-4d47-9d78-63d19acda77a

import Mathlib
import Definitions.Def_IntMul_HvdH_BApprox
import Definitions.Def_IntMul_HvdH_FPApprox
import Theorems.Thm_IntMul_HvdH_Sapprox_bound
import Theorems.Thm_IntMul_HvdH_Dapprox_bound
import Theorems.Thm_IntMul_HvdH_Japprox_bound

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Resample

open Complex Real

namespace IntMul.HvdH.Res

/-! ### Definitions (HvdH §2.4, §4.1) -/

/-- Normalised DFT `(F_n u)_j = n⁻¹ ∑_k e^{-2πi jk/n} u_k` on `ℤ/n`. -/
noncomputable def dftN (n : ℕ) [NeZero n] (u : ZMod n → ℂ) : ZMod n → ℂ :=
  fun j => (n : ℂ)⁻¹ * ∑ k : ZMod n, ZMod.stdAddChar (-(j * k)) * u k

/-- Resampling map `S : ℂ^s → ℂ^t`,
`(S u)_k = α⁻¹ ∑_{j ∈ ℤ} exp(-π α⁻² s² (k/t - j/s)²) u_{j mod s}`. -/
noncomputable def resS (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) : ZMod t → ℂ :=
  fun k => (α : ℂ)⁻¹ * ∑' j : ℤ,
    ((Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ) * u j

/-- Resampling map `T : ℂ^s → ℂ^t`,
`(T u)_k = ∑_{j ∈ ℤ} exp(-π α² t² (k/t - j/s)²) u_{j mod s}`. -/
noncomputable def resT (s t : ℕ) (α : ℝ) (u : ZMod s → ℂ) : ZMod t → ℂ :=
  fun k => ∑' j : ℤ,
    ((Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ) * u j

/-- `(P_s u)_j = u_{t j}`. -/
def permS (s t : ℕ) (u : ZMod s → ℂ) : ZMod s → ℂ := fun j => u ((t : ZMod s) * j)

/-- `(P_t u)_k = u_{-s k}`. -/
def permT (s t : ℕ) (u : ZMod t → ℂ) : ZMod t → ℂ := fun k => u (-((s : ZMod t) * k))

/-! ### Gaussian sums -/

lemma summable_gauss {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : c ≠ 0) (b : ℝ) :
    Summable (fun j : ℤ => Real.exp (-a * (c * j - b) ^ 2)) := by
  have hτ : 0 < (I * ((a * c ^ 2 / π : ℝ) : ℂ)).im := by
    have : 0 < c ^ 2 := by positivity
    rw [mul_im, I_re, I_im, ofReal_re, ofReal_im]
    simp only [zero_mul, one_mul, zero_add]
    positivity
  have h := ((summable_jacobiTheta₂_term_iff (I * ((-a * c * b / π : ℝ) : ℂ))
    (I * ((a * c ^ 2 / π : ℝ) : ℂ))).mpr hτ).norm
  have h2 := h.mul_left (Real.exp (-a * b ^ 2))
  refine h2.congr (fun n => ?_)
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im]
  field_simp
  ring

lemma summable_gauss_mul {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : c ≠ 0) (b : ℝ) (f : ℤ → ℂ)
    (B : ℝ) (hf : ∀ j, ‖f j‖ ≤ B) :
    Summable (fun j : ℤ => ((Real.exp (-a * (c * j - b) ^ 2) : ℝ) : ℂ) * f j) := by
  refine Summable.of_norm_bounded ((summable_gauss ha c hc b).mul_right B) (fun j => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hf j) (Real.exp_pos _).le

lemma poisson_shift (α : ℝ) (hα : 0 < α) (s : ℝ) (hs : 0 < s) (x ρ : ℝ) :
    ∑' j : ℤ, ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * (x - j / s) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * ρ * j / s)
      = α * ∑' n : ℤ, ((Real.exp (-π * α ^ 2 * (n - ρ / s) ^ 2) : ℝ) : ℂ) *
        cexp (-2 * π * I * s * x * (n - ρ / s)) := by
  set a : ℂ := ((α⁻¹ ^ 2 : ℝ) : ℂ) with ha_def
  set b : ℂ := ((α⁻¹ ^ 2 * s * x : ℝ) : ℂ) + I * (ρ / s : ℝ) with hb_def
  have ha : 0 < a.re := by rw [ha_def, ofReal_re]; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha b
  have hsqrt : a ^ (1 / 2 : ℂ) = (α⁻¹ : ℂ) := by
    rw [ha_def, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    push_cast; ring
  have hα0 : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hL : ∀ j : ℤ, ((Real.exp (-π * α⁻¹ ^ 2 * s ^ 2 * (x - j / s) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * ρ * j / s) =
      cexp (-π * α⁻¹ ^ 2 * s ^ 2 * x ^ 2) * cexp (-π * a * j ^ 2 + 2 * π * b * j) := by
    intro j
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [a, b]
    push_cast
    field_simp
    ring
  have hR : ∀ n : ℤ, cexp (-π * α⁻¹ ^ 2 * s ^ 2 * x ^ 2) * cexp (-π / a * (n + I * b) ^ 2) =
      ((Real.exp (-π * α ^ 2 * (n - ρ / s) ^ 2) : ℝ) : ℂ) *
        cexp (-2 * π * I * s * x * (n - ρ / s)) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e1 : (n : ℂ) + I * b = ((n : ℂ) - ρ / s) + I * (α⁻¹ ^ 2 * s * x) := by
      simp only [b]; push_cast; linear_combination (ρ / s : ℂ) * I_sq
    rw [e1]
    simp only [a]
    push_cast
    field_simp
    linear_combination (-(s : ℂ) ^ 4 * x ^ 2) * I_sq
  simp_rw [hL]
  rw [tsum_mul_left, hP, hsqrt, ← mul_assoc, mul_comm _ (1 / (α⁻¹ : ℂ)), mul_assoc,
    ← tsum_mul_left]
  simp_rw [hR]
  congr 1
  field_simp

/-! ### Characters -/

/-- The character `j ↦ e^{2πi ρ j / n}`. -/
noncomputable def ch (n : ℕ) [NeZero n] (ρ : ZMod n) : ZMod n → ℂ := fun j => ZMod.stdAddChar (ρ * j)

lemma norm_stdAddChar {n : ℕ} [NeZero n] (x : ZMod n) : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

lemma sum_stdAddChar_mul {n : ℕ} [NeZero n] (b : ZMod n) :
    ∑ x : ZMod n, (ZMod.stdAddChar (x * b) : ℂ) = if b = 0 then (n : ℂ) else 0 := by
  rw [AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar n)]
  simp [ZMod.card]

lemma dftN_ch {n : ℕ} [NeZero n] (ρ : ZMod n) :
    dftN n (ch n ρ) = fun j => if j = ρ then 1 else 0 := by
  ext j
  simp only [dftN, ch]
  have : ∀ k : ZMod n, (ZMod.stdAddChar (-(j * k)) : ℂ) * ZMod.stdAddChar (ρ * k) =
      ZMod.stdAddChar (k * (ρ - j)) := by
    intro k; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp_rw [this, sum_stdAddChar_mul, sub_eq_zero]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  split_ifs with h1 h2 h2
  · field_simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

lemma dft_inversion {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    u = fun j => ∑ ρ : ZMod n, dftN n u ρ * ch n ρ j := by
  ext j
  simp only [dftN, ch, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ k ρ : ZMod n, (n : ℂ)⁻¹ * ((ZMod.stdAddChar (-(ρ * k)) : ℂ) * u k) *
      ZMod.stdAddChar (ρ * j) = (n : ℂ)⁻¹ * u k * ZMod.stdAddChar (ρ * (j - k)) := by
    intro k ρ
    rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← neg_mul]; ring
  simp_rw [this, ← Finset.mul_sum]
  have hs : ∀ k : ZMod n, ∑ ρ : ZMod n, (ZMod.stdAddChar (ρ * (j - k)) : ℂ) =
      if j - k = 0 then (n : ℂ) else 0 := fun k => sum_stdAddChar_mul _
  simp_rw [hs, sub_eq_zero]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [Finset.sum_eq_single j]
  · simp; field_simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-! ### Linearity -/

section lin
variable {s t : ℕ} [NeZero s] [NeZero t]

lemma bound_pi (u : ZMod s → ℂ) (j : ℤ) : ‖u j‖ ≤ ∑ k, ‖u k‖ :=
  Finset.single_le_sum (f := fun k => ‖u k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

lemma summable_resS_term (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) (x : ℝ) :
    Summable (fun j : ℤ =>
      ((Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * (x - j / s) ^ 2) : ℝ) : ℂ) * u j) := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have := summable_gauss_mul (a := π * α⁻¹ ^ 2) (by positivity) 1 one_ne_zero (s * x)
    (fun j => u j) _ (bound_pi u)
  refine this.congr (fun j => ?_)
  congr 3
  field_simp
  ring

lemma summable_resT_term (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) (x : ℝ) :
    Summable (fun j : ℤ =>
      ((Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * (x - j / s) ^ 2) : ℝ) : ℂ) * u j) := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have := summable_gauss_mul (a := π * α ^ 2) (by positivity) ((t : ℝ) / s)
    (div_ne_zero ht hs) (t * x) (fun j => u j) _ (bound_pi u)
  refine this.congr (fun j => ?_)
  congr 3
  field_simp
  ring

lemma resS_sum (α : ℝ) (hα : 0 < α) (c : ZMod s → ℂ) (f : ZMod s → ZMod s → ℂ) (k : ZMod t) :
    resS s t α (fun j => ∑ ρ, c ρ * f ρ j) k = ∑ ρ, c ρ * resS s t α (f ρ) k := by
  simp only [resS]
  set K : ℤ → ℂ := fun j =>
    ((Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ)
  have hK : ∀ ρ, Summable (fun j : ℤ => K j * f ρ j) :=
    fun ρ => summable_resS_term α hα (f ρ) _
  have e1 : (∑' j : ℤ, K j * ∑ ρ, c ρ * f ρ j) = ∑ ρ, ∑' j : ℤ, c ρ * (K j * f ρ j) := by
    rw [← Summable.tsum_finsetSum (fun ρ _ => (hK ρ).mul_left (c ρ))]
    congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext ρ; ring
  rw [e1]
  simp_rw [tsum_mul_left, Finset.mul_sum]
  congr 1; ext ρ; ring

lemma resT_sum (α : ℝ) (hα : 0 < α) (c : ZMod s → ℂ) (f : ZMod s → ZMod s → ℂ) (k : ZMod t) :
    resT s t α (fun j => ∑ ρ, c ρ * f ρ j) k = ∑ ρ, c ρ * resT s t α (f ρ) k := by
  simp only [resT]
  set K : ℤ → ℂ := fun j =>
    ((Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ)
  have hK : ∀ ρ, Summable (fun j : ℤ => K j * f ρ j) :=
    fun ρ => summable_resT_term α hα (f ρ) _
  have e1 : (∑' j : ℤ, K j * ∑ ρ, c ρ * f ρ j) = ∑ ρ, ∑' j : ℤ, c ρ * (K j * f ρ j) := by
    rw [← Summable.tsum_finsetSum (fun ρ _ => (hK ρ).mul_left (c ρ))]
    congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext ρ; ring
  rw [e1]
  simp_rw [tsum_mul_left]
  rfl

end lin

/-! ### The resampling identity (HvdH Theorem 4.2) -/

section ident
variable {s t : ℕ} [NeZero s] [NeZero t]

lemma dftN_sum {n : ℕ} [NeZero n] {ι : Type*} [Fintype ι] (c : ι → ℂ) (f : ι → ZMod n → ℂ)
    (κ : ZMod n) : dftN n (fun l => ∑ ρ, c ρ * f ρ l) κ = ∑ ρ, c ρ * dftN n (f ρ) κ := by
  simp only [dftN, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext ρ; congr 1; ext l; ring

lemma resS_ch (α : ℝ) (hα : 0 < α) (ρ : ZMod s) (l : ZMod t) :
    resS s t α (ch s ρ) l = ∑' n : ℤ,
      ((Real.exp (-π * α ^ 2 * ((n : ℝ) - ρ.val / s) ^ 2) : ℝ) : ℂ) *
        ZMod.stdAddChar ((((ρ.val : ℤ) - s * n : ℤ) : ZMod t) * l) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hch : ∀ j : ℤ, ch s ρ (j : ZMod s) =
      cexp (2 * π * I * ((ρ.val : ℝ) : ℂ) * j / ((s : ℝ) : ℂ)) := by
    intro j
    simp only [ch]
    have : ρ * (j : ZMod s) = (((ρ.val : ℤ) * j : ℤ) : ZMod s) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  simp only [resS]
  simp_rw [hch]
  rw [poisson_shift α hα (s : ℝ) hs ((l.val : ℝ) / t) (ρ.val : ℝ), ← mul_assoc,
    inv_mul_cancel₀ hα', one_mul]
  congr 1; ext n
  congr 1
  have : (((ρ.val : ℤ) - s * n : ℤ) : ZMod t) * l = ((((ρ.val : ℤ) - s * n) * l.val : ℤ) : ZMod t) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.stdAddChar_coe]
  congr 1; push_cast; field_simp; ring

lemma dftN_tsum {n : ℕ} [NeZero n] (w : ℤ → ℂ) (hw : Summable (fun m => ‖w m‖)) (m : ℤ → ZMod n)
    (κ : ZMod n) :
    dftN n (fun l => ∑' i : ℤ, w i * ZMod.stdAddChar (m i * l)) κ =
      ∑' i : ℤ, w i * (if m i = κ then 1 else 0) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hsum : ∀ l : ZMod n, Summable (fun i : ℤ =>
      (ZMod.stdAddChar (-(κ * l)) : ℂ) * (w i * ZMod.stdAddChar (m i * l))) := by
    intro l
    refine Summable.of_norm_bounded hw (fun i => ?_)
    rw [norm_mul, norm_mul, norm_stdAddChar, norm_stdAddChar]; simp
  simp only [dftN]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun l _ => hsum l), ← tsum_mul_left]
  congr 1; ext i
  have e : ∀ l : ZMod n, (ZMod.stdAddChar (-(κ * l)) : ℂ) * (w i * ZMod.stdAddChar (m i * l)) =
      w i * ZMod.stdAddChar (l * (m i - κ)) := by
    intro l
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]; congr 2; ring
  simp_rw [e, ← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero]
  split_ifs <;> simp <;> field_simp

lemma reindex (α : ℝ) (ρ : ZMod s) (k : ZMod t) :
    ∑' n : ℤ, ((Real.exp (-π * α ^ 2 * ((n : ℝ) - ρ.val / s) ^ 2) : ℝ) : ℂ) *
        (if (((ρ.val : ℤ) - s * n : ℤ) : ZMod t) = -((s : ZMod t) * k) then 1 else 0)
      = ∑' j : ℤ, ((Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ) *
        (if (t : ZMod s) * (j : ZMod s) = ρ then 1 else 0) := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hsZ : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne t
  classical
  set F : ℤ → ℂ := fun N => ((Real.exp (-π * α ^ 2 * ((N : ℝ) / s) ^ 2) : ℝ) : ℂ) *
      (if (N : ZMod s) = -ρ ∧ (N : ZMod t) = (s : ZMod t) * k then 1 else 0) with hF
  have h1 : ∑' n : ℤ, ((Real.exp (-π * α ^ 2 * ((n : ℝ) - ρ.val / s) ^ 2) : ℝ) : ℂ) *
        (if (((ρ.val : ℤ) - s * n : ℤ) : ZMod t) = -((s : ZMod t) * k) then 1 else 0)
      = ∑' N, F N := by
    have hinj : Function.Injective (fun n : ℤ => (s : ℤ) * n - ρ.val) := by
      intro a b h; simp only at h
      exact mul_left_cancel₀ hsZ (by linarith)
    rw [← hinj.tsum_eq (f := F)]
    · congr 1; ext n
      simp only [F]
      congr 1
      · congr 2; push_cast; field_simp
      · have hA : (((s : ℤ) * n - ρ.val : ℤ) : ZMod s) = -ρ := by
          push_cast; rw [ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
        have hB : (((s : ℤ) * n - ρ.val : ℤ) : ZMod t) = (s : ZMod t) * k ↔
            (((ρ.val : ℤ) - s * n : ℤ) : ZMod t) = -((s : ZMod t) * k) := by
          push_cast
          constructor <;> intro h <;> linear_combination -h
        simp only [hA, true_and, hB]
    · intro N hN
      simp only [F, Function.mem_support, ne_eq, mul_eq_zero, ite_eq_right_iff,
        not_or, not_forall] at hN
      obtain ⟨_, ⟨hNs, _⟩, _⟩ := hN
      have : ((N + ρ.val : ℤ) : ZMod s) = 0 := by
        push_cast; rw [hNs, ZMod.natCast_zmod_val]; ring
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by simp only; linarith⟩
  have h2 : ∑' j : ℤ, ((Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2) : ℝ) : ℂ) *
        (if (t : ZMod s) * (j : ZMod s) = ρ then 1 else 0) = ∑' N, F N := by
    have hinj : Function.Injective (fun j : ℤ => (s : ℤ) * k.val - t * j) := by
      intro a b h; simp only at h
      exact mul_left_cancel₀ htZ (by linarith)
    rw [← hinj.tsum_eq (f := F)]
    · congr 1; ext j
      simp only [F]
      congr 1
      · congr 2; push_cast; field_simp
      · have hA : (((s : ℤ) * k.val - t * j : ℤ) : ZMod s) = -ρ ↔ (t : ZMod s) * (j : ZMod s) = ρ := by
          push_cast; rw [ZMod.natCast_self]
          constructor <;> intro h <;> linear_combination -h
        have hB : (((s : ℤ) * k.val - t * j : ℤ) : ZMod t) = (s : ZMod t) * k := by
          push_cast; rw [ZMod.natCast_self, ZMod.natCast_zmod_val]; ring
        simp only [hA, hB, and_true]
    · intro N hN
      simp only [F, Function.mem_support, ne_eq, mul_eq_zero, ite_eq_right_iff,
        not_or, not_forall] at hN
      obtain ⟨_, ⟨_, hNt⟩, _⟩ := hN
      have : (((s : ℤ) * k.val - N : ℤ) : ZMod t) = 0 := by
        push_cast; rw [hNt, ZMod.natCast_zmod_val]; ring
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by simp only; linarith⟩
  rw [h1, h2]

/-- **HvdH Theorem 4.2 (resampling identity).** `T P_s F_s = P_t F_t S`. -/
theorem resampling_identity (α : ℝ) (hα : 0 < α) (u : ZMod s → ℂ) :
    resT s t α (permS s t (dftN s u)) = permT s t (dftN t (resS s t α u)) := by
  ext k
  set v := dftN s u with hv
  -- left side
  have hL : permS s t v = fun j => ∑ ρ, v ρ * (if (t : ZMod s) * j = ρ then 1 else 0) := by
    ext j; simp [permS]
  rw [hL, resT_sum α hα]
  -- right side
  have hu : resS s t α u = fun l => ∑ ρ, v ρ * resS s t α (ch s ρ) l := by
    ext l
    conv_lhs => rw [dft_inversion u]
    rw [resS_sum α hα]
  rw [hu]
  simp only [permT]
  rw [dftN_sum]
  congr 1; ext ρ; congr 1
  have hw : Summable (fun n : ℤ =>
      ‖((Real.exp (-π * α ^ 2 * ((n : ℝ) - ρ.val / s) ^ 2) : ℝ) : ℂ)‖) := by
    have := summable_gauss (a := π * α ^ 2) (by positivity) 1 one_ne_zero (ρ.val / s)
    refine this.congr (fun n => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    congr 1; ring
  have := dftN_tsum _ hw (fun n => (((ρ.val : ℤ) - s * n : ℤ) : ZMod t)) (-((s : ZMod t) * k))
  have hS : resS s t α (ch s ρ) = fun l => ∑' n : ℤ,
      ((Real.exp (-π * α ^ 2 * ((n : ℝ) - ρ.val / s) ^ 2) : ℝ) : ℂ) *
        ZMod.stdAddChar ((((ρ.val : ℤ) - s * n : ℤ) : ZMod t) * l) :=
    funext (resS_ch α hα ρ)
  rw [hS, this, reindex]
  rfl

end ident

end IntMul.HvdH.Res

end Resample

section Bounds

open Real

namespace IntMul.HvdH.Res

lemma hasSum_geom_int {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℤ => r ^ n.natAbs) ((1 + r) / (1 - r)) := by
  have h1 : HasSum (fun n : ℕ => r ^ ((n : ℤ).natAbs)) (1 / (1 - r)) := by
    simpa [one_div] using hasSum_geometric_of_lt_one hr0 hr1
  have h2 : HasSum (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) (r / (1 - r)) := by
    have e : (fun n : ℕ => r ^ ((-((n : ℤ) + 1)).natAbs)) = fun n : ℕ => r * r ^ n := by
      funext n; rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, pow_succ, mul_comm]
    rw [e, div_eq_mul_inv]; exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have : 1 - r ≠ 0 := by linarith
  rw [show (1 + r) / (1 - r) = 1 / (1 - r) + r / (1 - r) by field_simp]
  exact h1.of_nat_of_neg_add_one h2

/-- If `0 ≤ f n ≤ C r^{|n|}` then `∑ f ≤ C (1+r)/(1-r)`. -/
lemma tsum_int_le_geom (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ C * r ^ n.natAbs) :
    Summable f ∧ ∑' n, f n ≤ C * ((1 + r) / (1 - r)) := by
  have hg := (hasSum_geom_int hr0 hr1).mul_left C
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hf hg.summable
  exact ⟨hs, hg.tsum_eq ▸ hs.tsum_le_tsum hf hg.summable⟩

/-- Variant excluding `n = 0`: if `f 0 = 0` and `0 ≤ f n ≤ C r^{|n|}` then `∑ f ≤ 2 C r/(1-r)`. -/
lemma tsum_int_le_geom' (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hz : f 0 = 0) {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hf : ∀ n, n ≠ 0 → f n ≤ C * r ^ n.natAbs) :
    Summable f ∧ ∑' n, f n ≤ 2 * C * r / (1 - r) := by
  have hC : ∀ n : ℤ, n ≠ 0 → 0 ≤ C * r ^ n.natAbs := fun n hn => (hf0 n).trans (hf n hn)
  set g : ℤ → ℝ := fun n => if n = 0 then 0 else C * r ^ n.natAbs
  have hg' := (hasSum_geom_int hr0 hr1).mul_left C
  have hg : HasSum g (C * ((1 + r) / (1 - r)) - C) := by
    have := hg'.update 0 0
    have hgu : g = Function.update (fun i : ℤ => C * r ^ i.natAbs) 0 0 := by
      funext n; by_cases h : n = 0 <;> simp [g, h]
    have e : C * ((1 + r) / (1 - r)) - C = 0 - C * r ^ Int.natAbs 0 + C * ((1 + r) / (1 - r)) := by
      simp only [Int.natAbs_zero, pow_zero, mul_one]; ring
    rw [hgu, e]; exact this
  have hfg : ∀ n, f n ≤ g n := by
    intro n; simp only [g]; split_ifs with h
    · rw [h, hz]
    · exact hf n h
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hfg hg.summable
  refine ⟨hs, (hs.tsum_le_tsum hfg hg.summable).trans (le_of_eq ?_)⟩
  rw [hg.tsum_eq]
  have : 1 - r ≠ 0 := by linarith
  field_simp; ring

/-- Key inequality of Lemma 4.6. -/
lemma key_ineq {q b1 b2 : ℝ} (hq : 1 ≤ q) (hb1 : |b1| ≤ 1 / 2) (hb2 : |b2| ≤ 1 / 2) {h : ℤ}
    (hh : h ≠ 0) : 2 * (q - 1) * (|(h : ℝ)| - 1 / 2) ^ 2 ≤ (q * h + b1) ^ 2 - b2 ^ 2 := by
  have ha : 1 ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hb2' : b2 ^ 2 ≤ 1 / 4 := by
    have := sq_abs b2 ▸ pow_le_pow_left₀ (abs_nonneg b2) hb2 2; nlinarith
  -- |q h + b1| ≥ q (|h| - 1/2)
  have h1 : q * (|(h : ℝ)| - 1 / 2) ≤ |q * h + b1| := by
    have e1 : |q * (h : ℝ)| = q * |(h : ℝ)| := by rw [abs_mul, abs_of_pos (by linarith)]
    have := abs_sub_abs_le_abs_sub (q * (h : ℝ)) (-b1)
    rw [sub_neg_eq_add, abs_neg, e1] at this
    nlinarith
  have h2 : 0 ≤ q * (|(h : ℝ)| - 1 / 2) := by nlinarith
  have h3 : (q * (|(h : ℝ)| - 1 / 2)) ^ 2 ≤ (q * h + b1) ^ 2 := by
    rw [← sq_abs (q * (h : ℝ) + b1)]; exact pow_le_pow_left₀ h2 h1 2
  rw [mul_pow] at h3
  set X := (|(h : ℝ)| - 1 / 2) ^ 2
  have e1 : 2 * q - 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have e2 : 1 / 4 ≤ X := by simp only [X]; nlinarith
  have e3 : (2 * q - 1) * X ≤ q ^ 2 * X := mul_le_mul_of_nonneg_right e1 (sq_nonneg _)
  nlinarith

lemma exp_neg_two_pi_le : Real.exp (-2 * π) ≤ 1 / 26 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * π) (by positivity)
  rw [show -2 * π = -(2 * π) by ring, Real.exp_neg]
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith

lemma exp_neg_pi_half_le : Real.exp (-π / 2) ≤ 1 / 4.3 := by
  have hpi := Real.pi_gt_d2
  have h := Real.quadratic_le_exp_of_nonneg (x := π / 4) (by positivity)
  have e : Real.exp (π / 2) = Real.exp (π / 4) * Real.exp (π / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq : 2.09 ≤ Real.exp (π / 4) := by nlinarith
  have h2 : 4.3 ≤ Real.exp (π / 2) := by rw [e]; nlinarith
  rw [show -π / 2 = -(π / 2) by ring, Real.exp_neg, inv_eq_one_div,
    div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

/-- Numerical inequality behind Lemma 4.6: for `x ≥ 1`,
`2 e^{-πx/2} / (1 - e^{-2πx}) < 2^{-x}`. -/
lemma numeric_E {x : ℝ} (hx : 1 ≤ x) :
    2 * Real.exp (-π * x / 2) / (1 - Real.exp (-2 * π * x)) < (2 : ℝ) ^ (-x) := by
  have hpi := Real.pi_gt_d2
  have hl := Real.log_two_lt_d9
  have hr : Real.exp (-2 * π * x) ≤ 1 / 26 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_two_pi_le
    nlinarith [Real.pi_pos]
  have hr0 := Real.exp_pos (-2 * π * x)
  set A := Real.exp (-x * Real.log 2) with hA
  have hApos : 0 < A := Real.exp_pos _
  have h2x : (2 : ℝ) ^ (-x) = A := by
    rw [Real.rpow_def_of_pos two_pos, hA]; ring_nf
  rw [h2x, div_lt_iff₀ (by linarith)]
  have hsplit : Real.exp (-π * x / 2) = A * Real.exp (-x * (π / 2 - Real.log 2)) := by
    rw [hA, ← Real.exp_add]; ring_nf
  have hmono : Real.exp (-x * (π / 2 - Real.log 2)) ≤ Real.exp (-(π / 2 - Real.log 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hval : Real.exp (-(π / 2 - Real.log 2)) = 2 * Real.exp (-π / 2) := by
    rw [show -(π / 2 - Real.log 2) = Real.log 2 + -π / 2 by ring, Real.exp_add,
      Real.exp_log two_pos]
  have hb := exp_neg_pi_half_le
  have : Real.exp (-x * (π / 2 - Real.log 2)) ≤ 2 / 4.3 := by
    rw [hval] at hmono; linarith
  rw [hsplit]
  nlinarith

end IntMul.HvdH.Res

end Bounds

section Maps

open Complex Real


namespace IntMul.HvdH.Res

/-- nearest integer `[x] = ⌊x + 1/2⌋` -/
noncomputable def rnd (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

lemma abs_sub_rnd_le (x : ℝ) : |x - rnd x| ≤ 1 / 2 := by
  unfold rnd
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

section maps
variable {s t : ℕ} [NeZero s] [NeZero t]

variable (s t) in
/-- `β_j = ⟨t j / s⟩` -/
noncomputable def beta (j : ℤ) : ℝ := (t : ℝ) * j / s - rnd ((t : ℝ) * j / s)

omit [NeZero s] [NeZero t] in
lemma abs_beta_le (j : ℤ) : |beta s t j| ≤ 1 / 2 := abs_sub_rnd_le _

omit [NeZero t] in
lemma beta_periodic (j q : ℤ) : beta s t (j + s * q) = beta s t j := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  unfold beta rnd
  have e : (t : ℝ) * ((j + s * q : ℤ) : ℝ) / s + 1 / 2 =
      ((t : ℝ) * j / s + 1 / 2) + ((t * q : ℤ) : ℝ) := by
    push_cast; field_simp; try ring
  have e2 : (t : ℝ) * ((j + s * q : ℤ) : ℝ) / s = (t : ℝ) * j / s + ((t * q : ℤ) : ℝ) := by
    push_cast; field_simp; try ring
  rw [e, Int.floor_add_intCast, e2]
  try (push_cast; ring)

omit [NeZero t] in
lemma beta_val (j : ℤ) : beta s t ((j : ZMod s).val : ℤ) = beta s t j := by
  rw [ZMod.val_intCast]
  conv_rhs => rw [← Int.emod_add_mul_ediv j s]
  rw [beta_periodic]

variable (s t) in
/-- Row selection `C : ℂ^t → ℂ^s`, `(C v)_l = v_{[t l / s]}`. -/
noncomputable def rowSel (v : ZMod t → ℂ) : ZMod s → ℂ :=
  fun l => v ((rnd ((t : ℝ) * l.val / s) : ℤ) : ZMod t)

variable (s t) in
/-- Diagonal map `(D_c u)_l = e^{c π α² β_l²} u_l` (`c = 1`: the map `D` of §4.2). -/
noncomputable def diagD (α c : ℝ) (u : ZMod s → ℂ) : ZMod s → ℂ :=
  fun l => ((Real.exp (c * π * α ^ 2 * beta s t l.val ^ 2) : ℝ) : ℂ) * u l

lemma diagD_diagD (α : ℝ) (u : ZMod s → ℂ) : diagD s t α 1 (diagD s t α (-1) u) = u := by
  ext l; simp only [diagD, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf; simp

lemma rnd_bounds (hst : s < t) (l : ZMod s) :
    0 ≤ rnd ((t : ℝ) * l.val / s) ∧ rnd ((t : ℝ) * l.val / s) < t := by
  have hs : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hl : (l.val : ℝ) + 1 ≤ s := by exact_mod_cast ZMod.val_lt l
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  constructor
  · unfold rnd; apply Int.floor_nonneg.mpr; positivity
  · unfold rnd; apply Int.floor_lt.mpr
    push_cast
    rw [div_add' _ _ _ hs.ne', div_lt_iff₀ hs]
    nlinarith

lemma val_rnd (hst : s < t) (l : ZMod s) :
    ((((rnd ((t : ℝ) * l.val / s) : ℤ) : ZMod t).val : ℝ)) = rnd ((t : ℝ) * l.val / s) := by
  obtain ⟨h0, h1⟩ := rnd_bounds hst l
  have := ZMod.val_intCast (n := t) (rnd ((t : ℝ) * l.val / s))
  rw [Int.emod_eq_of_lt h0 h1] at this
  exact_mod_cast this

/-- The normalised square system `N = C T D` of §4.2, entrywise. -/
lemma N_apply (hst : s < t) (α : ℝ) (u : ZMod s → ℂ) (l : ZMod s) :
    rowSel s t (resT s t α (diagD s t α 1 u)) l = ∑' j : ℤ,
      ((Real.exp (-π * α ^ 2 * (((t : ℝ) * j / s - rnd ((t : ℝ) * l.val / s)) ^ 2 -
        beta s t j ^ 2)) : ℝ) : ℂ) * u j := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have ht : (t : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne t
  simp only [rowSel, resT, diagD]
  rw [val_rnd hst]
  congr 1; ext j
  rw [beta_val, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  field_simp
  ring

/-- **Lemma 4.6, entrywise.** With `x = α² θ ≥ 1`,
`|(N u)_l - u_l| ≤ 2 e^{-πx/2}/(1 - e^{-2πx}) ‖u‖`. -/
lemma E_entry_bound (hst : s < t) (α : ℝ) (hα : 0 < α)
    (hx : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1)) (u : ZMod s → ℂ) (l : ZMod s) :
    ‖rowSel s t (resT s t α (diagD s t α 1 u)) l - u l‖ ≤
      2 * Real.exp (-π * (α ^ 2 * ((t : ℝ) / s - 1)) / 2) /
        (1 - Real.exp (-2 * π * (α ^ 2 * ((t : ℝ) / s - 1)))) * ‖u‖ := by
  set x := α ^ 2 * ((t : ℝ) / s - 1) with hxdef
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  have hs : (s : ℝ) ≠ 0 := hspos.ne'
  have hq : 1 ≤ (t : ℝ) / s := by
    rw [one_le_div hspos]; exact_mod_cast hst.le
  have hx0 : 0 ≤ x := by linarith
  set j0 : ℤ := (l.val : ℤ) with hj0
  set r := rnd ((t : ℝ) * l.val / s) with hr
  obtain ⟨K, hK⟩ : ∃ K : ℤ → ℝ, K = fun j =>
      Real.exp (-π * α ^ 2 * (((t : ℝ) * j / s - r) ^ 2 - beta s t j ^ 2)) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℝ, g = fun h : ℤ => if h = 0 then 0 else
      Real.exp (-2 * π * x * (|(h : ℝ)| - 1 / 2) ^ 2) := ⟨_, rfl⟩
  have hg0 : ∀ h, 0 ≤ g h := by
    intro h; simp only [hg]; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hgeom := tsum_int_le_geom' g hg0 (by simp [hg]) (C := Real.exp (3 * π * x / 2))
    (r := Real.exp (-2 * π * x)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])) (by
      intro h hh
      simp only [hg, hh, if_false]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : (h.natAbs : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [ha]
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hx0) (sq_nonneg (|(h : ℝ)| - 1))])
  have hK0 : K j0 = 1 := by
    simp only [hK, beta, hj0, hr, Int.cast_natCast, sub_self, Real.exp_zero, mul_zero]
  have hKg : ∀ j, j ≠ j0 → K j ≤ g (j - j0) := by
    intro j hj
    have hh : j - j0 ≠ 0 := sub_ne_zero.mpr hj
    rw [hK, hg]; simp only [hh, if_false]
    apply Real.exp_le_exp.mpr
    have key := key_ineq hq (abs_beta_le (s := s) (t := t) j0) (abs_beta_le (s := s) (t := t) j) hh
    have e : (t : ℝ) * j / s - r = (t : ℝ) / s * ((j - j0 : ℤ) : ℝ) + beta s t j0 := by
      simp only [beta, hj0, hr, Int.cast_natCast]; push_cast; ring
    rw [e]
    have hpa : 0 ≤ π * α ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left key hpa
    rw [hxdef]; push_cast at this ⊢
    linarith
  have hKnn : ∀ j, 0 ≤ K j := fun j => by rw [hK]; exact (Real.exp_pos _).le
  have hgs : Summable (fun j : ℤ => g (j - j0)) :=
    hgeom.1.comp_injective (sub_left_injective (b := j0))
  have hgsum : ∑' j : ℤ, g (j - j0) = ∑' h, g h := by
    have := (Equiv.subRight j0).tsum_eq g; simpa only [Equiv.subRight_apply] using this
  have hun : ∀ j : ℤ, ‖u j‖ ≤ ‖u‖ := fun j => norm_le_pi_norm u _
  have hsumm : Summable (fun j : ℤ => (K j : ℂ) * u j) := by
    refine Summable.of_norm_bounded
      ((hgs.add (hasSum_ite_eq j0 (1 : ℝ)).summable).mul_right ‖u‖) (fun j => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKnn j)]
    by_cases hj : j = j0
    · subst hj; simp [hK0]
      have h1 := hun j0; have h2 := hg0 0; nlinarith [norm_nonneg u]
    · simp only [hj, if_false, add_zero]
      exact mul_le_mul (hKg j hj) (hun j) (norm_nonneg _) (hg0 _)
  rw [N_apply hst]
  have hsplit := hsumm.tsum_eq_add_tsum_ite j0
  have hl : ((j0 : ℤ) : ZMod s) = l := by
    rw [hj0, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hKfun : (fun j : ℤ => ((Real.exp (-π * α ^ 2 * (((t : ℝ) * j / s -
      rnd ((t : ℝ) * l.val / s)) ^ 2 - beta s t j ^ 2)) : ℝ) : ℂ) * u j) =
      fun j : ℤ => (K j : ℂ) * u j := by rw [hK]
  rw [hKfun, hsplit, hK0, hl]
  simp only [Complex.ofReal_one, one_mul, add_sub_cancel_left]
  have hHS := (hgs.hasSum.mul_right ‖u‖)
  rw [hgsum] at hHS
  refine (tsum_of_norm_bounded hHS (fun j => ?_)).trans ?_
  · by_cases hj : j = j0
    · simp only [hj, if_true, norm_zero]; exact mul_nonneg (hg0 _) (norm_nonneg _)
    · simp only [hj, if_false]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hKnn j)]
      exact mul_le_mul (hKg j hj) (hun j) (norm_nonneg _) (hg0 _)
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    refine hgeom.2.trans (le_of_eq ?_)
    rw [mul_assoc 2, ← Real.exp_add]; ring_nf

end maps

end IntMul.HvdH.Res

end Maps

section Prop47

open Complex Real


namespace IntMul.HvdH.Res

section clm
variable {s t : ℕ} [NeZero s] [NeZero t]

/-- Bundle a linear map between finite coordinate spaces. -/
noncomputable def clmOf {a b : ℕ} [NeZero a] (f : (ZMod a → ℂ) → (ZMod b → ℂ))
    (hadd : ∀ u v, f (u + v) = f u + f v) (hsmul : ∀ (c : ℂ) u, f (c • u) = c • f u) :
    (ZMod a → ℂ) →L[ℂ] (ZMod b → ℂ) :=
  LinearMap.toContinuousLinearMap ⟨⟨f, hadd⟩, hsmul⟩

@[simp] lemma clmOf_apply {a b : ℕ} [NeZero a] (f : (ZMod a → ℂ) → (ZMod b → ℂ)) (hadd hsmul)
    (u : ZMod a → ℂ) : clmOf f hadd hsmul u = f u := rfl

lemma opNorm_le_of {a b : ℕ} [NeZero a] [NeZero b] (L : (ZMod a → ℂ) →L[ℂ] (ZMod b → ℂ))
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ u k, ‖L u k‖ ≤ M * ‖u‖) : ‖L‖ ≤ M :=
  L.opNorm_le_bound hM (fun u => (pi_norm_le_iff_of_nonneg (by positivity)).2 (h u))

lemma resS_add (α : ℝ) (hα : 0 < α) (u v : ZMod s → ℂ) :
    resS s t α (u + v) = resS s t α u + resS s t α v := by
  ext k; simp only [resS, Pi.add_apply, mul_add]
  rw [Summable.tsum_add (summable_resS_term α hα u _) (summable_resS_term α hα v _), mul_add]

lemma resS_smul (α : ℝ) (c : ℂ) (u : ZMod s → ℂ) :
    resS s t α (c • u) = c • resS s t α u := by
  ext k; simp only [resS, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr (fun j => by ring)

lemma resT_add (α : ℝ) (hα : 0 < α) (u v : ZMod s → ℂ) :
    resT s t α (u + v) = resT s t α u + resT s t α v := by
  ext k; simp only [resT, Pi.add_apply, mul_add]
  rw [Summable.tsum_add (summable_resT_term α hα u _) (summable_resT_term α hα v _)]

lemma resT_smul (α : ℝ) (c : ℂ) (u : ZMod s → ℂ) :
    resT s t α (c • u) = c • resT s t α u := by
  ext k; simp only [resT, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]; congr 1; ext j; ring

lemma diagD_add (α c : ℝ) (u v : ZMod s → ℂ) :
    diagD s t α c (u + v) = diagD s t α c u + diagD s t α c v := by
  ext l; simp [diagD, mul_add]

lemma diagD_smul (α c : ℝ) (a : ℂ) (u : ZMod s → ℂ) :
    diagD s t α c (a • u) = a • diagD s t α c u := by
  ext l; simp [diagD]; ring

/-- `‖(S u)_k‖ ≤ 2 ‖u‖` for `α ≥ 1` (a weak form of Lemma 4.5). -/
lemma resS_norm_le (α : ℝ) (hα : 1 ≤ α) (u : ZMod s → ℂ) (k : ZMod t) :
    ‖resS s t α u k‖ ≤ 2 * ‖u‖ := by
  have hα0 : 0 < α := by linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  set x : ℝ := (k.val : ℝ) / t
  set G : ℤ → ℝ := fun j => Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * (x - j / s) ^ 2) with hG
  have hGs : Summable G := by
    have := summable_resS_term (s := s) α hα0 (fun _ => (1 : ℂ)) x
    refine (this.norm).congr (fun j => ?_)
    simp only [G, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- Σ G = |α Σ_n e^{-πα²n²} ...| ≤ 2α
  have hP := poisson_shift α hα0 s hspos x 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one,
    sub_zero] at hP
  have htheta : ∑' n : ℤ, Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) ≤ 2 := by
    have h := tsum_int_le_geom (fun n : ℤ => Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2))
      (fun n => (Real.exp_pos _).le) (C := 1) (r := Real.exp (-π)) (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])) (fun n => by
        rw [one_mul, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
        have ha : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        rw [ha]
        have h1 : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
          rcases eq_or_ne n 0 with h | h
          · simp [h]
          · have : 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
            nlinarith [sq_abs (n : ℝ)]
        have hα2 : 1 ≤ α ^ 2 := by nlinarith
        have h2 : (n : ℝ) ^ 2 ≤ α ^ 2 * (n : ℝ) ^ 2 := by
          simpa [one_mul] using mul_le_mul_of_nonneg_right hα2 (sq_nonneg (n : ℝ))
        nlinarith [Real.pi_pos])
    refine h.2.trans ?_
    have hr : Real.exp (-π) ≤ 1 / 3 := by
      have := Real.add_one_le_exp π
      have h3 := Real.pi_gt_three
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
      linarith
    have hr0 := Real.exp_pos (-π)
    rw [one_mul, div_le_iff₀ (by linarith)]; linarith
  have hsumG : ∑' j, G j ≤ 2 * α := by
    have h1 : ((∑' j, G j : ℝ) : ℂ) = (α : ℂ) * ∑' n : ℤ,
        ((Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) * cexp (-2 * π * I * s * x * n) := by
      rw [Complex.ofReal_tsum]; exact hP
    have h2 : ‖∑' n : ℤ, ((Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
        cexp (-2 * π * I * s * x * n)‖ ≤ ∑' n : ℤ, Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) := by
      have hs2 : Summable (fun n : ℤ => Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2)) := by
        have := summable_gauss (a := π * α ^ 2) (by positivity) 1 one_ne_zero 0
        refine this.congr (fun n => ?_); congr 1; ring
      refine tsum_of_norm_bounded hs2.hasSum (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have : ‖cexp (-2 * π * I * s * x * n)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
    have h3 : |∑' j, G j| ≤ α * 2 := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hα0]
      exact mul_le_mul_of_nonneg_left (h2.trans htheta) hα0.le
    linarith [le_abs_self (∑' j, G j)]
  simp only [resS]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα0]
  have hb : ‖∑' j : ℤ, ((G j : ℝ) : ℂ) * u j‖ ≤ (∑' j, G j) * ‖u‖ := by
    refine tsum_of_norm_bounded (hGs.hasSum.mul_right ‖u‖) (fun j => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) (Real.exp_pos _).le
  calc α⁻¹ * ‖∑' j : ℤ, ((G j : ℝ) : ℂ) * u j‖ ≤ α⁻¹ * ((∑' j, G j) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ α⁻¹ * ((2 * α) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumG (norm_nonneg _))
          (by positivity)
    _ = 2 * ‖u‖ := by field_simp

lemma dftN_eq_dft {n : ℕ} [NeZero n] (u : ZMod n → ℂ) :
    dftN n u = (n : ℂ)⁻¹ • ZMod.dft u := by
  ext j; simp only [dftN, Pi.smul_apply, smul_eq_mul, ZMod.dft_apply]
  congr 1; refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_comm j k]

variable (s t) in
noncomputable def Smap (α : ℝ) (hα : 0 < α) : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  clmOf (resS s t α) (resS_add α hα) (resS_smul α)

variable (s t) in
noncomputable def Tmap (α : ℝ) (hα : 0 < α) : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  clmOf (resT s t α) (resT_add α hα) (resT_smul α)

variable (s t) in
noncomputable def Cmap : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  clmOf (rowSel s t) (fun _ _ => rfl) (fun _ _ => rfl)

variable (s t) in
noncomputable def Dmap (α : ℝ) : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  clmOf (diagD s t α 1) (diagD_add α 1) (diagD_smul α 1)

variable (s t) in
noncomputable def PTmap : (ZMod t → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  clmOf (permT s t) (fun _ _ => rfl) (fun _ _ => rfl)

variable (s t) in
/-- `(P_s⁻¹ w)_j = w_{t⁻¹ j}`. -/
noncomputable def PSinv : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  clmOf (fun w j => w ((t : ZMod s)⁻¹ * j)) (fun _ _ => rfl) (fun _ _ => rfl)

lemma PSinv_permS (hcop : Nat.Coprime s t) (w : ZMod s → ℂ) : PSinv s t (permS s t w) = w := by
  ext j; simp only [PSinv, clmOf_apply, permS]
  rw [← mul_assoc, ZMod.coe_mul_inv_eq_one t hcop.symm, one_mul]

lemma norm_Cmap_le : ‖Cmap s t‖ ≤ 1 :=
  opNorm_le_of _ zero_le_one (fun u l => by
    simp only [Cmap, clmOf_apply, rowSel, one_mul]; exact norm_le_pi_norm u _)

lemma norm_PTmap_le : ‖PTmap s t‖ ≤ 1 :=
  opNorm_le_of _ zero_le_one (fun u l => by
    simp only [PTmap, clmOf_apply, permT, one_mul]; exact norm_le_pi_norm u _)

lemma norm_PSinv_le : ‖PSinv s t‖ ≤ 1 :=
  opNorm_le_of _ zero_le_one (fun u l => by
    simp only [PSinv, clmOf_apply, one_mul]; exact norm_le_pi_norm u _)

lemma norm_Smap_le (α : ℝ) (hα : 1 ≤ α) : ‖Smap s t α (by linarith)‖ ≤ 2 :=
  opNorm_le_of _ (by norm_num) (fun u k => by
    simp only [Smap, clmOf_apply]; exact resS_norm_le α hα u k)

lemma norm_Dmap_le (α : ℝ) : ‖Dmap s t α‖ ≤ Real.exp (π * α ^ 2 / 4) :=
  opNorm_le_of _ (Real.exp_pos _).le (fun u l => by
    simp only [Dmap, clmOf_apply, diagD]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (Real.exp_le_exp.mpr ?_) (norm_le_pi_norm u _) (norm_nonneg _)
      (Real.exp_pos _).le
    have hb := abs_beta_le (s := s) (t := t) (l.val : ℤ)
    have hb2 : beta s t (l.val : ℤ) ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (beta s t (l.val : ℤ))]
    have : 0 ≤ π * α ^ 2 := by positivity
    nlinarith)

/-- A map within `1/2` of the identity has a right inverse of norm `≤ 2`, and is injective. -/
lemma exists_inv_near_id (L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (h : ∀ u, ‖L u - u‖ ≤ (1 / 2) * ‖u‖) :
    ∃ M : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ), ‖M‖ ≤ 2 ∧ (∀ v, L (M v) = v) ∧
      Function.Injective L := by
  have hlow : ∀ u, ‖u‖ ≤ 2 * ‖L u‖ := fun u => by
    have h1 := h u
    have h2 : ‖u‖ ≤ ‖L u‖ + ‖L u - u‖ := by
      calc ‖u‖ = ‖L u - (L u - u)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hinj : Function.Injective (L : (ZMod s → ℂ) →ₗ[ℂ] (ZMod s → ℂ)) := by
    refine (injective_iff_map_eq_zero _).2 (fun u hu => ?_)
    have := hlow u
    rw [show (L u) = 0 from hu, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  let e := LinearEquiv.ofBijective (L : (ZMod s → ℂ) →ₗ[ℂ] (ZMod s → ℂ)) ⟨hinj, hsurj⟩
  have he : ∀ v, L (e.symm v) = v := fun v => e.apply_symm_apply v
  refine ⟨LinearMap.toContinuousLinearMap e.symm.toLinearMap, ?_, fun v => he v, hinj⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
  have := hlow (e.symm v)
  rw [he v] at this
  exact this

lemma Nmap_near_id (hst : s < t) (α : ℝ) (hα : 0 < α) (hx : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    (u : ZMod s → ℂ) :
    ‖(Cmap s t).comp ((Tmap s t α hα).comp (Dmap s t α)) u - u‖ ≤ (1 / 2) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun l => ?_)
  have h := E_entry_bound hst α hα hx u l
  have h2 := numeric_E hx
  have h3 : (2 : ℝ) ^ (-(α ^ 2 * ((t : ℝ) / s - 1))) ≤ 1 / 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show -(α ^ 2 * ((t : ℝ) / s - 1)) ≤ -1 by linarith)
    rw [Real.rpow_neg_one] at this; linarith
  simp only [Pi.sub_apply, ContinuousLinearMap.comp_apply, Cmap, Tmap, Dmap, clmOf_apply]
  calc _ ≤ _ := h
    _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

lemma four_exp_le (α : ℕ) (hα : 2 ≤ α) :
    4 * Real.exp (π * (α : ℝ) ^ (2 : ℕ) / 4) ≤ (2 : ℝ) ^ (2 * α ^ 2) := by
  have hm : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ α := by exact_mod_cast hα
    nlinarith
  have hl := Real.log_two_gt_d9
  have hp := Real.pi_lt_d2
  have h4 : (4 : ℝ) * Real.exp (π * (α : ℝ) ^ (2 : ℕ) / 4) =
      Real.exp (2 * Real.log 2 + π * (α : ℝ) ^ (2 : ℕ) / 4) := by
    rw [Real.exp_add, ← Real.log_rpow two_pos, Real.exp_log (by positivity)]; norm_num
  rw [h4, ← Real.rpow_natCast (2 : ℝ) (2 * α ^ 2), Real.rpow_def_of_pos two_pos,
    Real.exp_le_exp]
  push_cast
  nlinarith

end clm

/-- **Harvey–van der Hoeven, Proposition 4.7(i).** For coprime `s < t` and an integer `α ≥ 2`
with `α² (t/s - 1) ≥ 1`, the normalised DFT of length `s` factors through the normalised
DFT of length `t` as `F_s = 2^{2α²} B F_t A` with `‖A‖, ‖B‖ ≤ 1` (sup norms). -/
theorem prop_4_7_i (s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u)) := by
  have hα1 : (1 : ℝ) ≤ α := by exact_mod_cast (show 1 ≤ α by omega)
  have hα0 : (0 : ℝ) < α := by linarith
  obtain ⟨M, hM, hNM, hNinj⟩ := exists_inv_near_id _ (Nmap_near_id hst (α : ℝ) hα0 hθ)
  set S := Smap s t (α : ℝ) hα0 with hS
  set Bc := (PSinv s t).comp ((Dmap s t (α : ℝ)).comp (M.comp ((Cmap s t).comp (PTmap s t))))
    with hBc
  have key : ∀ u, dftN s u = Bc (dftN t (S u)) := by
    intro u
    set w := dftN s u
    set y := diagD s t (α : ℝ) (-1) (permS s t w)
    have hy : (Cmap s t).comp ((Tmap s t α hα0).comp (Dmap s t α)) y =
        (Cmap s t) (PTmap s t (dftN t (S u))) := by
      simp only [ContinuousLinearMap.comp_apply, Cmap, Tmap, Dmap, PTmap, clmOf_apply, y,
        diagD_diagD, hS, Smap]
      rw [resampling_identity (α : ℝ) hα0 u]; rfl
    have hMy : M ((Cmap s t) (PTmap s t (dftN t (S u)))) = y :=
      hNinj (by rw [hNM, hy])
    simp only [hBc, ContinuousLinearMap.comp_apply, hMy]
    simp only [Dmap, clmOf_apply, y, diagD_diagD]
    exact (PSinv_permS hcop w).symm
  set c : ℂ := (2 : ℂ) ^ (2 * α ^ 2) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨(1 / 2 : ℂ) • S, c⁻¹ • (2 : ℂ) • Bc, ?_, ?_, fun u => ?_⟩
  · calc ‖(1 / 2 : ℂ) • S‖ ≤ ‖(1 / 2 : ℂ)‖ * ‖S‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ (1 / 2) * 2 := by
        rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (norm_Smap_le _ hα1) (by norm_num)
      _ = 1 := by norm_num
  · have hBc' : ‖Bc‖ ≤ Real.exp (π * (α : ℝ) ^ 2 / 4) * 2 := by
      have e1 := norm_PSinv_le (s := s) (t := t)
      have e2 := norm_Dmap_le (s := s) (t := t) (α : ℝ)
      have e3 := norm_Cmap_le (s := s) (t := t)
      have e4 := norm_PTmap_le (s := s) (t := t)
      calc ‖Bc‖ ≤ ‖PSinv s t‖ * (‖Dmap s t (α : ℝ)‖ * (‖M‖ * (‖Cmap s t‖ * ‖PTmap s t‖))) := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
              (norm_nonneg _)
        _ ≤ 1 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * (2 * (1 * 1))) := by gcongr
        _ = _ := by ring
    have hcn : ‖c⁻¹‖ = ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ := by rw [hc]; simp
    have h4 := four_exp_le α hα
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2) := by positivity
    calc ‖c⁻¹ • (2 : ℂ) • Bc‖ ≤ ‖c⁻¹‖ * (‖(2 : ℂ)‖ * ‖Bc‖) :=
          (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _))
      _ ≤ ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ * (2 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * 2)) := by
          rw [hcn, show ‖(2 : ℂ)‖ = 2 by norm_num]; gcongr
      _ ≤ 1 := by
          rw [inv_mul_le_iff₀ hpos]; linarith
  · have h1 := key u
    rw [dftN_eq_dft, dftN_eq_dft] at h1
    rw [h1]
    have hSu : S u = (2 : ℂ) • (((1 / 2 : ℂ) • S) u) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul]; norm_num
    rw [hSu]
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_smul]
    congr 1
    field_simp

end IntMul.HvdH.Res

end Prop47

open Complex Real

namespace IntMul.HvdH.P47
open IntMul.HvdH IntMul.HvdH.Res

/-- A pair of integers as a Gaussian integer in `ℂ`. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

lemma rnd_eq (s t : ℕ) (hs : 0 < s) (j : ℤ) :
    rnd ((t : ℝ) * j / s) = (2 * t * j + s) / (2 * s) := by
  unfold rnd
  rw [Int.floor_eq_iff]
  have hs2 : (0 : ℤ) < 2 * s := by omega
  have h1 := Int.ediv_mul_le (2 * t * j + s) hs2.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (2 * t * j + s) hs2
  generalize (2 * (t : ℤ) * j + s) / (2 * s) = q at h1 h2 ⊢
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h1' : (q : ℝ) * (2 * s) ≤ 2 * t * j + s := by exact_mod_cast h1
  have h2' : (2 * t * j + s : ℝ) < (q + 1) * (2 * s) := by exact_mod_cast h2
  have e : (t : ℝ) * j / s + 1 / 2 = (2 * t * j + s) / (2 * s) := by field_simp; try ring
  rw [e, le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
  constructor <;> linarith

lemma beta_eq (s t : ℕ) (hs : 0 < s) (j : ℤ) : beta s t j = (bOf s t j : ℝ) / s := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold beta bOf; rw [rnd_eq s t hs]; push_cast; field_simp; try ring

lemma bOf_periodic (s t : ℕ) (hs : 0 < s) (j q : ℤ) : bOf s t (j + s * q) = bOf s t j := by
  unfold bOf
  have e : 2 * (t : ℤ) * (j + s * q) + s = (2 * t * j + s) + (t * q) * (2 * s) := by ring
  rw [e, Int.add_mul_ediv_right _ _ (by omega)]
  ring

lemma eKz_periodic (s t : ℕ) (hs : 0 < s) (j q h : ℤ) : eKz s t (j + s * q) h = eKz s t j h := by
  unfold eKz
  rw [bOf_periodic s t hs, show j + s * q + h = (j + h) + s * q by ring, bOf_periodic s t hs]

lemma Eexact_mod (s t α : ℕ) (hs : 0 < s) (f : ℕ → ℂ) (l : ℕ) :
    Eexact s t α f l = Eexact s t α f (l % s) := by
  unfold Eexact
  congr 1; funext h
  have hl : ((l % s : ℕ) : ℤ) = (l : ℤ) % s := Int.natCast_mod l s
  have e1 : eEx s t α (l : ℤ) h = eEx s t α ((l % s : ℕ) : ℤ) h := by
    unfold eEx; rw [hl]
    conv_lhs => rw [← Int.emod_add_mul_ediv (l : ℤ) s]
    rw [eKz_periodic s t hs]
  have e2 : ((l : ℤ) + h) % s = (((l % s : ℕ) : ℤ) + h) % s := by
    rw [hl]
    conv_lhs => rw [← Int.emod_add_mul_ediv (l : ℤ) s]
    rw [show (l : ℤ) % s + s * ((l : ℤ) / s) + h = ((l : ℤ) % s + h) + s * ((l : ℤ) / s) by ring,
      Int.add_mul_emod_self_left]
  rw [e1, e2]

/-- `x = α²θ`. -/
noncomputable def xθ (s t α : ℕ) : ℝ := ((α ^ 2 * (t - s) : ℕ) : ℝ) / s

lemma bOf_bounds (s t : ℕ) (hs : 0 < s) (l : ℤ) :
    -(s : ℤ) ≤ 2 * bOf s t l ∧ 2 * bOf s t l < s := by
  have hs2 : (0 : ℤ) < 2 * s := by omega
  have h1 := Int.ediv_mul_le (2 * t * l + s) hs2.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (2 * t * l + s) hs2
  unfold bOf
  generalize (2 * (t : ℤ) * l + s) / (2 * s) = q at h1 h2 ⊢
  constructor <;> nlinarith

lemma abs_b_le (s t : ℕ) (hs : 0 < s) (l : ℤ) : |(bOf s t l : ℝ) / s| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := bOf_bounds s t hs l
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h1' : -(s : ℝ) ≤ 2 * bOf s t l := by exact_mod_cast h1
  have h2' : 2 * (bOf s t l : ℝ) ≤ s := by exact_mod_cast h2.le
  rw [abs_div, abs_of_pos hsR, div_le_iff₀ hsR, abs_le]
  constructor <;> linarith

lemma eEx_nonneg (s t α : ℕ) (l h : ℤ) : 0 ≤ eEx s t α l h := by
  unfold eEx; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma eEx_le_gauss (s t α : ℕ) (hs : 0 < s) (hst : s ≤ t) (l h : ℤ) (hh : h ≠ 0) :
    eEx s t α l h ≤ Real.exp (-2 * π * xθ s t α * (|(h : ℝ)| - 1 / 2) ^ 2) := by
  unfold eEx; rw [if_neg hh]
  apply Real.exp_le_exp.2
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hq : 1 ≤ (t : ℝ) / s := by rw [one_le_div hsR]; exact_mod_cast hst
  have key := key_ineq hq (abs_b_le s t hs l) (abs_b_le s t hs (l + h)) hh
  have hK : (eKz s t l h : ℝ) / s ^ 2 =
      ((t : ℝ) / s * h + (bOf s t l : ℝ) / s) ^ 2 - ((bOf s t (l + h) : ℝ) / s) ^ 2 := by
    unfold eKz; push_cast; field_simp
  have hx : xθ s t α = α ^ 2 * ((t : ℝ) / s - 1) := by
    unfold xθ; rw [Nat.cast_mul, Nat.cast_sub hst]; push_cast; field_simp
  have hpa : (0 : ℝ) ≤ π * α ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left key hpa
  rw [← hK] at this
  rw [hx]
  have e : π * α ^ 2 * (eKz s t l h : ℝ) / s ^ 2 = π * α ^ 2 * ((eKz s t l h : ℝ) / s ^ 2) := by ring
  rw [e]; nlinarith

lemma eEx_summable (s t α : ℕ) (hs : 0 < s) (hst : s ≤ t) (hx : 1 ≤ xθ s t α) (l : ℤ) :
    Summable (eEx s t α l) := by
  set x := xθ s t α
  have hx0 : 0 ≤ x := by linarith
  exact (tsum_int_le_geom' (eEx s t α l) (eEx_nonneg s t α l) (by simp [eEx])
    (C := Real.exp (3 * π * x / 2)) (r := Real.exp (-2 * π * x)) (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])) (by
      intro h hh
      refine (eEx_le_gauss s t α hs hst l h hh).trans ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ha : (h.natAbs : ℝ) = |(h : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [ha]
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hx0) (sq_nonneg (|(h : ℝ)| - 1))])).1

lemma lam0_le {x : ℝ} (hx : 1 ≤ x) :
    2 * Real.exp (-π * x / 2) / (1 - Real.exp (-2 * π * x)) ≤ 0.49 := by
  have hpi := Real.pi_gt_d2
  have h1 : Real.exp (-π * x / 2) ≤ 1 / 4.3 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_pi_half_le
    nlinarith [Real.pi_pos]
  have h2 : Real.exp (-2 * π * x) ≤ 1 / 26 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_two_pi_le
    nlinarith [Real.pi_pos]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (-2 * π * x)]

section
variable {s t : ℕ} [NeZero s] [NeZero t]

/-- The square system `N = C T D` is `I + E` with `E` the map of Lemma 4.11. -/
lemma N_eq (hst : s < t) (α : ℕ) (hx : 1 ≤ xθ s t α) (w : ZMod s → ℂ) (l : ZMod s) :
    rowSel s t (resT s t α (diagD s t α 1 w)) l =
      w l + Eexact s t α (fun i => w (i : ZMod s)) l.val := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rw [N_apply hst]
  set L : ℤ := (l.val : ℤ)
  -- each term
  have hterm : ∀ h : ℤ, ((Real.exp (-π * (α : ℝ) ^ 2 * (((t : ℝ) * ((L + h : ℤ) : ℝ) / s -
      rnd ((t : ℝ) * l.val / s)) ^ 2 - beta s t (L + h) ^ 2)) : ℝ) : ℂ) * w ((L + h : ℤ) : ZMod s)
      = (if h = 0 then w l else 0) +
        ((eEx s t α L h : ℝ) : ℂ) * w ((((L + h) % s).toNat : ℕ) : ZMod s) := by
    intro h
    have hw : ((((L + h) % s).toNat : ℕ) : ZMod s) = ((L + h : ℤ) : ZMod s) := by
      have h0 : 0 ≤ (L + h) % s := Int.emod_nonneg _ (by exact_mod_cast hs.ne')
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ZMod.intCast_mod]
    rw [hw]
    have hr : ((rnd ((t : ℝ) * l.val / s) : ℤ) : ℝ) = (t : ℝ) * L / s - (bOf s t L : ℝ) / s := by
      have := beta_eq s t hs L
      unfold beta at this
      simp only [L, Int.cast_natCast] at this ⊢
      linarith
    have hexp : -π * (α : ℝ) ^ 2 * (((t : ℝ) * ((L + h : ℤ) : ℝ) / s -
        rnd ((t : ℝ) * l.val / s)) ^ 2 - beta s t (L + h) ^ 2) =
        -(π * α ^ 2 * (eKz s t L h : ℝ) / s ^ 2) := by
      rw [hr, beta_eq s t hs]; unfold eKz; push_cast; field_simp; ring
    rw [hexp]
    by_cases hh : h = 0
    · subst hh
      have : eKz s t L 0 = 0 := by unfold eKz; simp
      rw [this]
      simp [eEx, L]
    · simp [hh, eEx]
  rw [← (Equiv.addLeft L).tsum_eq]
  simp only [Equiv.coe_addLeft]
  rw [tsum_congr hterm]
  have hs1 : Summable (fun h : ℤ => if h = 0 then w l else 0) :=
    (hasSum_ite_eq (0 : ℤ) (w l)).summable
  have hs2 : Summable (fun h : ℤ => ((eEx s t α L h : ℝ) : ℂ) * w ((((L + h) % s).toNat : ℕ) : ZMod s)) := by
    refine Summable.of_norm_bounded ((eEx_summable s t α hs hst.le hx L).mul_right ‖w‖) (fun h => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (eEx_nonneg s t α _ _)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w _) (eEx_nonneg s t α _ _)
  rw [hs1.tsum_add hs2, tsum_ite_eq]
  rfl

end

lemma d_le_one (α : ℕ) (hα : 2 ≤ α) (β : ℝ) (hb1 : |β| ≤ 1 / 2) :
    |Real.exp (Real.pi * α ^ 2 * β ^ 2) / (2 : ℝ) ^ (2 * α ^ 2 - 2)| ≤ 1 := by
  have h4 := four_exp_le α hα
  rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
  have hb2 : β ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg β]
  have h0 : 0 ≤ Real.pi * α ^ 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hb2 h0
  have : Real.exp (Real.pi * α ^ 2 * β ^ 2) ≤ Real.exp (π * (α : ℝ) ^ (2 : ℕ) / 4) := by
    apply Real.exp_le_exp.2; linarith
  have hk : 2 * α ^ 2 = (2 * α ^ 2 - 2) + 2 := by
    have : 2 ≤ 2 * α ^ 2 := by nlinarith
    omega
  have e : (2 : ℝ) ^ (2 * α ^ 2) = 2 ^ (2 * α ^ 2 - 2) * 4 := by
    conv_lhs => rw [hk]
    rw [pow_add]; norm_num
  rw [e] at h4
  linarith

/-- **Harvey–van der Hoeven, Proposition 4.7.** For coprime `s < t`, an integer `2 ≤ α` with
`α² ≤ p` and `α²θ ≥ 1`, there are maps `A`, `B` of norm `≤ 1` with `F_s = 2^{2α²} B F_t A`, and the
computable maps `Sapprox` and `Bapprox` approximate `2^p A` and `2^p B` on fixed-point vectors. -/
theorem prop_4_7 (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      (∀ U : ℕ → ℤ × ℤ, (∀ i, ‖toC (U i)‖ ≤ 2 ^ p) → ∀ k : ZMod t,
        ‖toC (Sapprox p s t α U k.val) - 2 ^ p * A (fun j => toC (U j.val) / 2 ^ p) k‖
          ≤ 6 * sWidth p α + 4) ∧
      (∀ V : ℕ → ℤ × ℤ, (∀ i, ‖toC (V i)‖ ≤ 2 ^ p) → ∀ j : ZMod s,
        ‖toC (Bapprox p s t α V j.val) - 2 ^ p * B (fun k => toC (V k.val) / 2 ^ p) j‖
          ≤ jIter p s t α * (10 * eWidth p α + 12) + 4) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hα1 : (1 : ℝ) ≤ α := by exact_mod_cast (show 1 ≤ α by omega)
  have hα0 : (0 : ℝ) < α := by linarith
  have hxθ : 1 ≤ xθ s t α := by
    unfold xθ; rw [le_div_iff₀ hsR, one_mul]; exact_mod_cast hx
  have hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by
    have e : xθ s t α = α ^ 2 * ((t : ℝ) / s - 1) := by
      unfold xθ; rw [Nat.cast_mul, Nat.cast_sub hst.le]; push_cast; field_simp
    rw [← e]; exact hxθ
  obtain ⟨M, hM, hNM, hNinj⟩ := exists_inv_near_id _ (Nmap_near_id hst (α : ℝ) hα0 hθ)
  set S := Smap s t (α : ℝ) hα0 with hS
  set Bc := (PSinv s t).comp ((Dmap s t (α : ℝ)).comp (M.comp ((Cmap s t).comp (PTmap s t))))
    with hBc
  have key : ∀ u, dftN s u = Bc (dftN t (S u)) := by
    intro u
    set w := dftN s u
    set y := diagD s t (α : ℝ) (-1) (permS s t w)
    have hy : (Cmap s t).comp ((Tmap s t α hα0).comp (Dmap s t α)) y =
        (Cmap s t) (PTmap s t (dftN t (S u))) := by
      simp only [ContinuousLinearMap.comp_apply, Cmap, Tmap, Dmap, PTmap, clmOf_apply, y,
        diagD_diagD, hS, Smap]
      rw [resampling_identity (α : ℝ) hα0 u]; rfl
    have hMy : M ((Cmap s t) (PTmap s t (dftN t (S u)))) = y :=
      hNinj (by rw [hNM, hy])
    simp only [hBc, ContinuousLinearMap.comp_apply, hMy]
    simp only [Dmap, clmOf_apply, y, diagD_diagD]
    exact (PSinv_permS hcop w).symm
  set c : ℂ := (2 : ℂ) ^ (2 * α ^ 2) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 := four_exp_le α hα
  refine ⟨(1 / 2 : ℂ) • S, c⁻¹ • (2 : ℂ) • Bc, ?_, ?_, fun u => ?_, ?_, ?_⟩
  · calc ‖(1 / 2 : ℂ) • S‖ ≤ ‖(1 / 2 : ℂ)‖ * ‖S‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ (1 / 2) * 2 := by
        rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (norm_Smap_le _ hα1) (by norm_num)
      _ = 1 := by norm_num
  · have hBc' : ‖Bc‖ ≤ Real.exp (π * (α : ℝ) ^ 2 / 4) * 2 := by
      have e1 := norm_PSinv_le (s := s) (t := t)
      have e2 := norm_Dmap_le (s := s) (t := t) (α : ℝ)
      have e3 := norm_Cmap_le (s := s) (t := t)
      have e4 := norm_PTmap_le (s := s) (t := t)
      calc ‖Bc‖ ≤ ‖PSinv s t‖ * (‖Dmap s t (α : ℝ)‖ * (‖M‖ * (‖Cmap s t‖ * ‖PTmap s t‖))) := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
              (norm_nonneg _)
        _ ≤ 1 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * (2 * (1 * 1))) := by gcongr
        _ = _ := by ring
    have hcn : ‖c⁻¹‖ = ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ := by rw [hc]; simp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2) := by positivity
    calc ‖c⁻¹ • (2 : ℂ) • Bc‖ ≤ ‖c⁻¹‖ * (‖(2 : ℂ)‖ * ‖Bc‖) :=
          (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _))
      _ ≤ ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ * (2 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * 2)) := by
          rw [hcn, show ‖(2 : ℂ)‖ = 2 by norm_num]; gcongr
      _ ≤ 1 := by
          rw [inv_mul_le_iff₀ hpos]; linarith
  · have h1 := key u
    rw [dftN_eq_dft, dftN_eq_dft] at h1
    rw [h1]
    have hSu : S u = (2 : ℂ) • (((1 / 2 : ℂ) • S) u) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul]; norm_num
    rw [hSu]
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_smul]
    congr 1
    field_simp
  · -- Lemma 4.9
    intro U hU k
    have hb := Sapprox_bound p s t α k.val hs (by omega) hα hαp U hU
    have e : Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k.val =
        ((1 / 2 : ℂ) • S) (fun j => toC (U j.val) / 2 ^ p) k := by
      simp only [ContinuousLinearMap.smul_apply, hS, Smap, clmOf_apply, resS, Pi.smul_apply,
        smul_eq_mul, Sexact]
      rw [← mul_assoc, ← tsum_mul_left]
      congr 1; funext j
      have hj : ((j : ZMod s).val) = (j % s).toNat := by
        have h0 : 0 ≤ j % s := Int.emod_nonneg _ (by exact_mod_cast hs.ne')
        have := ZMod.val_intCast (n := s) j
        omega
      rw [hj]
      simp only [toC]
      have hexp : -(Real.pi * ((j : ℝ) - (s * k.val : ℝ) / t) ^ 2 / α ^ 2) =
          -π * (α : ℝ)⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2 := by
        have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
        field_simp; ring
      rw [hexp]; push_cast; ring
    rw [e] at hb; exact hb
  · -- Lemmas 4.8 and 4.12
    intro V hV j
    set n := jIter p s t α
    set m := eWidth p α
    set εJ : ℝ := n * (10 * m + 12) + 1 with hεJ
    have hp' : 100 * εJ ≤ 2 ^ p := by
      have : ((100 * (n * (10 * m + 12) + 1) : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this; rw [hεJ]; linarith
    have hn1 : 1 ≤ n := by
      simp only [n, jIter]
      rw [Nat.le_div_iff_mul_le (by omega)]
      have : 1 ≤ p * s := Nat.mul_pos (by nlinarith) hs
      omega
    have hpB : 2 * (10 * m + 12) ≤ 2 ^ p := by
      have : 10 * m + 12 ≤ n * (10 * m + 12) := Nat.le_mul_of_pos_left _ hn1
      omega
    have hpR : (0 : ℝ) < 2 ^ p := by positivity
    set v : ZMod t → ℂ := fun k => toC (V k.val) / 2 ^ p with hv
    have hvb : ∀ k, ‖v k‖ ≤ 1 := by
      intro k; simp only [hv]; rw [norm_div, norm_pow, Complex.norm_two, div_le_one hpR]; exact hV _
    set y : ZMod s → ℂ := Cmap s t (PTmap s t v) with hy
    have hyb : ‖y‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun l => ?_)
      simp only [hy, Cmap, PTmap, clmOf_apply, rowSel, permT]; exact hvb _
    set w₀ : ZMod s → ℂ := (1 / 2 : ℂ) • M y with hw₀
    -- N w₀ = y / 2
    have hNw : (Cmap s t).comp ((Tmap s t α hα0).comp (Dmap s t α)) w₀ = (1 / 2 : ℂ) • y := by
      rw [hw₀, ContinuousLinearMap.map_smul, hNM]
    have hN : ∀ l, rowSel s t (resT s t α (diagD s t α 1 w₀)) l = y l / 2 := by
      intro l
      have := congrFun hNw l
      change rowSel s t (resT s t α (diagD s t α 1 w₀)) l = (1 / 2 : ℂ) * y l at this
      rw [this]; ring
    have hw₀b : ‖w₀‖ ≤ 0.99 := by
      have hE := fun l => E_entry_bound hst (α : ℝ) hα0 hθ w₀ l
      have hl := lam0_le hθ
      have : ‖w₀‖ ≤ 1 / 2 + 0.49 * ‖w₀‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun l => ?_)
        have h1 := hE l
        rw [hN l] at h1
        have h2 : ‖y l / 2‖ ≤ 1 / 2 := by
          rw [norm_div, Complex.norm_two]; linarith [norm_le_pi_norm y l]
        have h3 : ‖w₀ l‖ ≤ ‖y l / 2‖ + ‖y l / 2 - w₀ l‖ := by
          have := norm_sub_le (y l / 2) (y l / 2 - w₀ l); simpa using this
        rw [norm_sub_rev] at h1
        have h4 : 2 * Real.exp (-π * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) / 2) /
            (1 - Real.exp (-2 * π * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)))) * ‖w₀‖ ≤ 0.49 * ‖w₀‖ :=
          mul_le_mul_of_nonneg_right hl (norm_nonneg _)
        rw [norm_sub_rev] at h3
        linarith
      linarith
    -- the ℕ-indexed data
    set Y := cSel s t (ptPerm s t V) with hY
    set wN : ℕ → ℂ := fun i => w₀ (i : ZMod s) with hwN
    have hYy : ∀ l : ℕ, toC (Y l) / 2 ^ p = y (l : ZMod s) := by
      intro l
      have hq : ((((2 * t * (l % s) + s) / (2 * s) : ℕ)) : ℤ) =
          (2 * t * ((l % s : ℕ) : ℤ) + s) / (2 * s) := by push_cast; ring_nf
      show toC (V (-((s : ZMod t) * (((((2 * t * (l % s) + s) / (2 * s) : ℕ) : ZMod t)).val : ZMod t))).val) / 2 ^ p =
        toC (V (-((s : ZMod t) * ((rnd ((t : ℝ) * ((l : ZMod s).val : ℕ) / s) : ℤ) : ZMod t))).val) / 2 ^ p
      have hr := rnd_eq s t hs ((l % s : ℕ) : ℤ)
      rw [Int.cast_natCast] at hr
      rw [ZMod.natCast_zmod_val, ZMod.val_natCast, hr, ← hq, Int.cast_natCast]
    have hJ : ∀ l, wN l + Eexact s t α wN l = toC (Y l) / 2 ^ p / 2 := by
      intro l
      rw [Eexact_mod s t α hs, hYy l, ← hN (l : ZMod s), N_eq hst α hxθ w₀ (l : ZMod s),
        ZMod.val_natCast]
    have hwNb : ∀ l, ‖wN l‖ ≤ 0.99 := fun l => (norm_le_pi_norm w₀ _).trans hw₀b
    set Z := Japprox p s t α Y with hZ
    have hJb := Japprox_bound p s t α hs hx hpB Y (fun i => by
        simp only [hY, cSel, ptPerm]; exact hV _) wN (fun l => (hwNb l).trans (by norm_num)) hJ
    have hZb : ∀ l, ‖toC (Z l)‖ ≤ 2 ^ p := by
      intro l
      have h1 := hJb l
      have h2 : ‖(2 : ℂ) ^ p * wN l‖ ≤ 2 ^ p * 0.99 := by
        rw [norm_mul, norm_pow, Complex.norm_two]; exact mul_le_mul_of_nonneg_left (hwNb l) hpR.le
      have h3 := norm_le_insert' (toC (Z l)) ((2 : ℂ) ^ p * wN l)
      change ‖toC (Z l) - 2 ^ p * wN l‖ ≤ εJ at h1
      linarith
    set l₀ : ℕ := ((t : ZMod s)⁻¹ * j).val with hl₀
    have hDb := Dapprox_bound p s t α hs hα hαp Z hZb l₀
    have hl₀Z : ((l₀ : ℕ) : ZMod s) = (t : ZMod s)⁻¹ * j := by
      rw [hl₀, ZMod.natCast_zmod_val]
    have hk : 2 * α ^ 2 = (2 * α ^ 2 - 2) + 2 := by
      have : 2 ≤ 2 * α ^ 2 := by nlinarith
      omega
    set d : ℝ := Real.exp (Real.pi * α ^ 2 * ((t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋) ^ 2) /
        2 ^ (2 * α ^ 2 - 2) with hd
    have hBv : (c⁻¹ • (2 : ℂ) • Bc) v j = (d : ℂ) * wN l₀ := by
      have h1 : (c⁻¹ • (2 : ℂ) • Bc) v j = c⁻¹ * (2 * (((Real.exp (1 * π * α ^ 2 *
          beta s t (l₀ : ℤ) ^ 2) : ℝ) : ℂ) * M y ((t : ZMod s)⁻¹ * j))) := rfl
      have h2 : wN l₀ = (1 / 2 : ℂ) * M y ((t : ZMod s)⁻¹ * j) := by
        simp only [hwN, hl₀Z, hw₀]; rfl
      have hβ : beta s t (l₀ : ℤ) = (t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋ := by
        unfold beta rnd; push_cast; ring_nf
      have h3 : c = 2 ^ (2 * α ^ 2 - 2) * 4 := by
        rw [hc]; conv_lhs => rw [hk]
        rw [pow_add]; norm_num
      rw [h1, h2, hβ, hd, h3]
      generalize M y ((t : ZMod s)⁻¹ * j) = z
      push_cast
      field_simp
      ring
    have hd1 : |d| ≤ 1 := by
      have hb1 : |(t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋| ≤ 1 / 2 := by
        have := abs_sub_rnd_le ((t * l₀ : ℝ) / s); unfold rnd at this; exact this
      exact d_le_one α hα _ hb1
    have hBapp : Bapprox p s t α V j.val = Dapprox p s t α Z l₀ := by
      simp only [Bapprox, psInvPerm, ZMod.natCast_zmod_val]
      rfl
    rw [hBapp, hBv]
    change ‖toC (Dapprox p s t α Z l₀) - (d : ℂ) * toC (Z l₀)‖ < 3 at hDb
    have hsplit : toC (Dapprox p s t α Z l₀) - 2 ^ p * ((d : ℂ) * wN l₀) =
        (toC (Dapprox p s t α Z l₀) - (d : ℂ) * toC (Z l₀)) + (d : ℂ) * (toC (Z l₀) - 2 ^ p * wN l₀) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h5 : |d| * ‖toC (Z l₀) - 2 ^ p * wN l₀‖ ≤ 1 * εJ :=
      mul_le_mul hd1 (hJb l₀) (norm_nonneg _) zero_le_one
    have : ((n : ℕ) : ℝ) * (10 * m + 12) + 4 = εJ + 3 := by rw [hεJ]; ring
    rw [this]; linarith


lemma resS_norm_le_tight {s t : ℕ} [NeZero s] [NeZero t] (α : ℝ) (hα : 2 ≤ α) (u : ZMod s → ℂ) (k : ZMod t) :
    ‖resS s t α u k‖ ≤ 1.1 * ‖u‖ := by
  have hα0 : 0 < α := by linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  set x : ℝ := (k.val : ℝ) / t
  set G : ℤ → ℝ := fun j => Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * (x - j / s) ^ 2) with hG
  have hGs : Summable G := by
    have := summable_resS_term (s := s) α hα0 (fun _ => (1 : ℂ)) x
    refine (this.norm).congr (fun j => ?_)
    simp only [G, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- Σ G = |α Σ_n e^{-πα²n²} ...| ≤ 2α
  have hP := poisson_shift α hα0 s hspos x 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one,
    sub_zero] at hP
  have htheta : ∑' n : ℤ, Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) ≤ 1.1 := by
    have h := tsum_int_le_geom (fun n : ℤ => Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2))
      (fun n => (Real.exp_pos _).le) (C := 1) (r := Real.exp (-(4 * π))) (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])) (fun n => by
        rw [one_mul, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
        have ha : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        rw [ha]
        have h1 : |(n : ℝ)| ≤ (n : ℝ) ^ 2 := by
          rcases eq_or_ne n 0 with h | h
          · simp [h]
          · have : 1 ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
            nlinarith [sq_abs (n : ℝ)]
        have hα2 : 4 ≤ α ^ 2 := by nlinarith
        have h2 : 4 * (n : ℝ) ^ 2 ≤ α ^ 2 * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hα2 (sq_nonneg (n : ℝ))
        have h3 : 4 * |(n : ℝ)| ≤ α ^ 2 * (n : ℝ) ^ 2 := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h3 Real.pi_pos.le])
    refine h.2.trans ?_
    have hr : Real.exp (-(4 * π)) ≤ 1 / 21 := by
      have := Real.quadratic_le_exp_of_nonneg (x := 4 * π) (by positivity)
      have h3 := Real.pi_gt_three
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
      nlinarith
    have hr0 := Real.exp_pos (-(4 * π))
    rw [one_mul, div_le_iff₀ (by linarith)]; linarith
  have hsumG : ∑' j, G j ≤ 1.1 * α := by
    have h1 : ((∑' j, G j : ℝ) : ℂ) = (α : ℂ) * ∑' n : ℤ,
        ((Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) * cexp (-2 * π * I * s * x * n) := by
      rw [Complex.ofReal_tsum]; exact hP
    have h2 : ‖∑' n : ℤ, ((Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
        cexp (-2 * π * I * s * x * n)‖ ≤ ∑' n : ℤ, Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2) := by
      have hs2 : Summable (fun n : ℤ => Real.exp (-π * α ^ 2 * (n : ℝ) ^ 2)) := by
        have := summable_gauss (a := π * α ^ 2) (by positivity) 1 one_ne_zero 0
        refine this.congr (fun n => ?_); congr 1; ring
      refine tsum_of_norm_bounded hs2.hasSum (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have : ‖cexp (-2 * π * I * s * x * n)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
    have h3 : |∑' j, G j| ≤ α * 1.1 := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hα0]
      exact mul_le_mul_of_nonneg_left (h2.trans htheta) hα0.le
    linarith [le_abs_self (∑' j, G j)]
  simp only [resS]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα0]
  have hb : ‖∑' j : ℤ, ((G j : ℝ) : ℂ) * u j‖ ≤ (∑' j, G j) * ‖u‖ := by
    refine tsum_of_norm_bounded (hGs.hasSum.mul_right ‖u‖) (fun j => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u _) (Real.exp_pos _).le
  calc α⁻¹ * ‖∑' j : ℤ, ((G j : ℝ) : ℂ) * u j‖ ≤ α⁻¹ * ((∑' j, G j) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ α⁻¹ * ((1.1 * α) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumG (norm_nonneg _))
          (by positivity)
    _ = 1.1 * ‖u‖ := by field_simp


lemma eight_exp_le (α : ℕ) (hα : 2 ≤ α) :
    8 * Real.exp (π * (α : ℝ) ^ (2 : ℕ) / 4) ≤ (2 : ℝ) ^ (2 * α ^ 2) := by
  have hm : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ α := by exact_mod_cast hα
    nlinarith
  have hl := Real.log_two_gt_d9
  have hp := Real.pi_lt_d2
  have h8 : (8 : ℝ) * Real.exp (π * (α : ℝ) ^ (2 : ℕ) / 4) =
      Real.exp (3 * Real.log 2 + π * (α : ℝ) ^ (2 : ℕ) / 4) := by
    rw [Real.exp_add, ← Real.log_rpow two_pos, Real.exp_log (by positivity)]; norm_num
  rw [h8, ← Real.rpow_natCast (2 : ℝ) (2 * α ^ 2), Real.rpow_def_of_pos two_pos,
    Real.exp_le_exp]
  push_cast
  nlinarith

lemma Sexact_add_t (s t α : ℕ) (ht : 0 < t) (u : ℕ → ℂ) (k : ℕ) :
    Sexact s t α u (k + t) = Sexact s t α u k := by
  unfold Sexact
  rw [← (Equiv.addRight (s : ℤ)).tsum_eq]
  congr 1; funext j
  simp only [Equiv.coe_addRight]
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : ((j + (s : ℤ) : ℤ) : ℝ) - (s : ℝ) * ((k + t : ℕ) : ℝ) / t = (j : ℝ) - (s : ℝ) * (k : ℝ) / t := by
    push_cast; field_simp; ring
  have e2 : (j + (s : ℤ)) % s = j % s := by simp
  rw [e1, e2]

lemma Sexact_mod (s t α : ℕ) (ht : 0 < t) (u : ℕ → ℂ) (k : ℕ) :
    Sexact s t α u k = Sexact s t α u (k % t) := by
  have h : ∀ q r : ℕ, Sexact s t α u (r + t * q) = Sexact s t α u r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [show r + t * (q + 1) = (r + t * q) + t by ring, Sexact_add_t s t α ht, ih]
  conv_lhs => rw [← Nat.mod_add_div k t]
  exact h _ _

/-- **Harvey–van der Hoeven, Proposition 4.7.** For coprime `s < t`, an integer `2 ≤ α` with
`α² ≤ p` and `α²θ ≥ 1`, there are maps `A`, `B` of norm `≤ 1` with `F_s = 2^{2α²} B F_t A`, and the
computable maps `Sapprox` and `Bapprox` approximate `2^p A` and `2^p B` on fixed-point vectors. -/
theorem prop_4_7_core (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 11 / 20 ∧ ‖B‖ ≤ 1 / 2 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      (∀ U : ℕ → ℤ × ℤ, (∀ i, ‖toC (U i)‖ ≤ 2 ^ p) → ∀ k : ℕ,
        ‖toC (Sapprox p s t α U k) - 2 ^ p * A (fun j => toC (U j.val) / 2 ^ p) (k : ZMod t)‖
          ≤ 6 * sWidth p α + 4) ∧
      (∀ V : ℕ → ℤ × ℤ, (∀ i, ‖toC (V i)‖ ≤ 2 ^ p) → ∀ j : ZMod s,
        ‖toC (Bapprox p s t α V j.val) - 2 ^ p * B (fun k => toC (V k.val) / 2 ^ p) j‖
          ≤ jIter p s t α * (10 * eWidth p α + 12) + 4) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hα1 : (1 : ℝ) ≤ α := by exact_mod_cast (show 1 ≤ α by omega)
  have hα0 : (0 : ℝ) < α := by linarith
  have hxθ : 1 ≤ xθ s t α := by
    unfold xθ; rw [le_div_iff₀ hsR, one_mul]; exact_mod_cast hx
  have hθ : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by
    have e : xθ s t α = α ^ 2 * ((t : ℝ) / s - 1) := by
      unfold xθ; rw [Nat.cast_mul, Nat.cast_sub hst.le]; push_cast; field_simp
    rw [← e]; exact hxθ
  obtain ⟨M, hM, hNM, hNinj⟩ := exists_inv_near_id _ (Nmap_near_id hst (α : ℝ) hα0 hθ)
  set S := Smap s t (α : ℝ) hα0 with hS
  set Bc := (PSinv s t).comp ((Dmap s t (α : ℝ)).comp (M.comp ((Cmap s t).comp (PTmap s t))))
    with hBc
  have key : ∀ u, dftN s u = Bc (dftN t (S u)) := by
    intro u
    set w := dftN s u
    set y := diagD s t (α : ℝ) (-1) (permS s t w)
    have hy : (Cmap s t).comp ((Tmap s t α hα0).comp (Dmap s t α)) y =
        (Cmap s t) (PTmap s t (dftN t (S u))) := by
      simp only [ContinuousLinearMap.comp_apply, Cmap, Tmap, Dmap, PTmap, clmOf_apply, y,
        diagD_diagD, hS, Smap]
      rw [resampling_identity (α : ℝ) hα0 u]; rfl
    have hMy : M ((Cmap s t) (PTmap s t (dftN t (S u)))) = y :=
      hNinj (by rw [hNM, hy])
    simp only [hBc, ContinuousLinearMap.comp_apply, hMy]
    simp only [Dmap, clmOf_apply, y, diagD_diagD]
    exact (PSinv_permS hcop w).symm
  set c : ℂ := (2 : ℂ) ^ (2 * α ^ 2) with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ two_ne_zero
  have h4 := four_exp_le α hα
  refine ⟨(1 / 2 : ℂ) • S, c⁻¹ • (2 : ℂ) • Bc, ?_, ?_, fun u => ?_, ?_, ?_⟩
  · have hS1 : ‖S‖ ≤ 1.1 := opNorm_le_of _ (by norm_num) (fun u k => by
      simp only [hS, Smap, clmOf_apply]
      exact resS_norm_le_tight (α : ℝ) (by exact_mod_cast hα) u k)
    calc ‖(1 / 2 : ℂ) • S‖ ≤ ‖(1 / 2 : ℂ)‖ * ‖S‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ (1 / 2) * 1.1 := by
        rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
        exact mul_le_mul_of_nonneg_left hS1 (by norm_num)
      _ = 11 / 20 := by norm_num
  · have hBc' : ‖Bc‖ ≤ Real.exp (π * (α : ℝ) ^ 2 / 4) * 2 := by
      have e1 := norm_PSinv_le (s := s) (t := t)
      have e2 := norm_Dmap_le (s := s) (t := t) (α : ℝ)
      have e3 := norm_Cmap_le (s := s) (t := t)
      have e4 := norm_PTmap_le (s := s) (t := t)
      calc ‖Bc‖ ≤ ‖PSinv s t‖ * (‖Dmap s t (α : ℝ)‖ * (‖M‖ * (‖Cmap s t‖ * ‖PTmap s t‖))) := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
              (norm_nonneg _)
        _ ≤ 1 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * (2 * (1 * 1))) := by gcongr
        _ = _ := by ring
    have hcn : ‖c⁻¹‖ = ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ := by rw [hc]; simp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * α ^ 2) := by positivity
    calc ‖c⁻¹ • (2 : ℂ) • Bc‖ ≤ ‖c⁻¹‖ * (‖(2 : ℂ)‖ * ‖Bc‖) :=
          (ContinuousLinearMap.opNorm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_smul_le _ _) (norm_nonneg _))
      _ ≤ ((2 : ℝ) ^ (2 * α ^ 2))⁻¹ * (2 * (Real.exp (π * (α : ℝ) ^ 2 / 4) * 2)) := by
          rw [hcn, show ‖(2 : ℂ)‖ = 2 by norm_num]; gcongr
      _ ≤ 1 / 2 := by
          have h8 := eight_exp_le α hα
          rw [inv_mul_le_iff₀ hpos]; linarith
  · have h1 := key u
    rw [dftN_eq_dft, dftN_eq_dft] at h1
    rw [h1]
    have hSu : S u = (2 : ℂ) • (((1 / 2 : ℂ) • S) u) := by
      rw [ContinuousLinearMap.smul_apply, smul_smul]; norm_num
    rw [hSu]
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_smul]
    congr 1
    field_simp
  · -- Lemma 4.9
    intro U hU k₀
    have hb := Sapprox_bound p s t α k₀ hs (by omega) hα hαp U hU
    set k : ZMod t := (k₀ : ZMod t)
    have hper : Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k₀ =
        Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k.val := by
      rw [Sexact_mod s t α (by omega), ZMod.val_natCast]
    have e : Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k.val =
        ((1 / 2 : ℂ) • S) (fun j => toC (U j.val) / 2 ^ p) k := by
      simp only [ContinuousLinearMap.smul_apply, hS, Smap, clmOf_apply, resS, Pi.smul_apply,
        smul_eq_mul, Sexact]
      rw [← mul_assoc, ← tsum_mul_left]
      congr 1; funext j
      have hj : ((j : ZMod s).val) = (j % s).toNat := by
        have h0 : 0 ≤ j % s := Int.emod_nonneg _ (by exact_mod_cast hs.ne')
        have := ZMod.val_intCast (n := s) j
        omega
      rw [hj]
      simp only [toC]
      have hexp : -(Real.pi * ((j : ℝ) - (s * k.val : ℝ) / t) ^ 2 / α ^ 2) =
          -π * (α : ℝ)⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k.val : ℝ) / t - j / s) ^ 2 := by
        have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
        field_simp; ring
      rw [hexp]; push_cast; ring
    rw [hper, e] at hb; exact hb
  · -- Lemmas 4.8 and 4.12
    intro V hV j
    set n := jIter p s t α
    set m := eWidth p α
    set εJ : ℝ := n * (10 * m + 12) + 1 with hεJ
    have hp' : 100 * εJ ≤ 2 ^ p := by
      have : ((100 * (n * (10 * m + 12) + 1) : ℕ) : ℝ) ≤ ((2 ^ p : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this; rw [hεJ]; linarith
    have hn1 : 1 ≤ n := by
      simp only [n, jIter]
      rw [Nat.le_div_iff_mul_le (by omega)]
      have : 1 ≤ p * s := Nat.mul_pos (by nlinarith) hs
      omega
    have hpB : 2 * (10 * m + 12) ≤ 2 ^ p := by
      have : 10 * m + 12 ≤ n * (10 * m + 12) := Nat.le_mul_of_pos_left _ hn1
      omega
    have hpR : (0 : ℝ) < 2 ^ p := by positivity
    set v : ZMod t → ℂ := fun k => toC (V k.val) / 2 ^ p with hv
    have hvb : ∀ k, ‖v k‖ ≤ 1 := by
      intro k; simp only [hv]; rw [norm_div, norm_pow, Complex.norm_two, div_le_one hpR]; exact hV _
    set y : ZMod s → ℂ := Cmap s t (PTmap s t v) with hy
    have hyb : ‖y‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun l => ?_)
      simp only [hy, Cmap, PTmap, clmOf_apply, rowSel, permT]; exact hvb _
    set w₀ : ZMod s → ℂ := (1 / 2 : ℂ) • M y with hw₀
    -- N w₀ = y / 2
    have hNw : (Cmap s t).comp ((Tmap s t α hα0).comp (Dmap s t α)) w₀ = (1 / 2 : ℂ) • y := by
      rw [hw₀, ContinuousLinearMap.map_smul, hNM]
    have hN : ∀ l, rowSel s t (resT s t α (diagD s t α 1 w₀)) l = y l / 2 := by
      intro l
      have := congrFun hNw l
      change rowSel s t (resT s t α (diagD s t α 1 w₀)) l = (1 / 2 : ℂ) * y l at this
      rw [this]; ring
    have hw₀b : ‖w₀‖ ≤ 0.99 := by
      have hE := fun l => E_entry_bound hst (α : ℝ) hα0 hθ w₀ l
      have hl := lam0_le hθ
      have : ‖w₀‖ ≤ 1 / 2 + 0.49 * ‖w₀‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun l => ?_)
        have h1 := hE l
        rw [hN l] at h1
        have h2 : ‖y l / 2‖ ≤ 1 / 2 := by
          rw [norm_div, Complex.norm_two]; linarith [norm_le_pi_norm y l]
        have h3 : ‖w₀ l‖ ≤ ‖y l / 2‖ + ‖y l / 2 - w₀ l‖ := by
          have := norm_sub_le (y l / 2) (y l / 2 - w₀ l); simpa using this
        rw [norm_sub_rev] at h1
        have h4 : 2 * Real.exp (-π * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) / 2) /
            (1 - Real.exp (-2 * π * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)))) * ‖w₀‖ ≤ 0.49 * ‖w₀‖ :=
          mul_le_mul_of_nonneg_right hl (norm_nonneg _)
        rw [norm_sub_rev] at h3
        linarith
      linarith
    -- the ℕ-indexed data
    set Y := cSel s t (ptPerm s t V) with hY
    set wN : ℕ → ℂ := fun i => w₀ (i : ZMod s) with hwN
    have hYy : ∀ l : ℕ, toC (Y l) / 2 ^ p = y (l : ZMod s) := by
      intro l
      have hq : ((((2 * t * (l % s) + s) / (2 * s) : ℕ)) : ℤ) =
          (2 * t * ((l % s : ℕ) : ℤ) + s) / (2 * s) := by push_cast; ring_nf
      show toC (V (-((s : ZMod t) * (((((2 * t * (l % s) + s) / (2 * s) : ℕ) : ZMod t)).val : ZMod t))).val) / 2 ^ p =
        toC (V (-((s : ZMod t) * ((rnd ((t : ℝ) * ((l : ZMod s).val : ℕ) / s) : ℤ) : ZMod t))).val) / 2 ^ p
      have hr := rnd_eq s t hs ((l % s : ℕ) : ℤ)
      rw [Int.cast_natCast] at hr
      rw [ZMod.natCast_zmod_val, ZMod.val_natCast, hr, ← hq, Int.cast_natCast]
    have hJ : ∀ l, wN l + Eexact s t α wN l = toC (Y l) / 2 ^ p / 2 := by
      intro l
      rw [Eexact_mod s t α hs, hYy l, ← hN (l : ZMod s), N_eq hst α hxθ w₀ (l : ZMod s),
        ZMod.val_natCast]
    have hwNb : ∀ l, ‖wN l‖ ≤ 0.99 := fun l => (norm_le_pi_norm w₀ _).trans hw₀b
    set Z := Japprox p s t α Y with hZ
    have hJb := Japprox_bound p s t α hs hx hpB Y (fun i => by
        simp only [hY, cSel, ptPerm]; exact hV _) wN (fun l => (hwNb l).trans (by norm_num)) hJ
    have hZb : ∀ l, ‖toC (Z l)‖ ≤ 2 ^ p := by
      intro l
      have h1 := hJb l
      have h2 : ‖(2 : ℂ) ^ p * wN l‖ ≤ 2 ^ p * 0.99 := by
        rw [norm_mul, norm_pow, Complex.norm_two]; exact mul_le_mul_of_nonneg_left (hwNb l) hpR.le
      have h3 := norm_le_insert' (toC (Z l)) ((2 : ℂ) ^ p * wN l)
      change ‖toC (Z l) - 2 ^ p * wN l‖ ≤ εJ at h1
      linarith
    set l₀ : ℕ := ((t : ZMod s)⁻¹ * j).val with hl₀
    have hDb := Dapprox_bound p s t α hs hα hαp Z hZb l₀
    have hl₀Z : ((l₀ : ℕ) : ZMod s) = (t : ZMod s)⁻¹ * j := by
      rw [hl₀, ZMod.natCast_zmod_val]
    have hk : 2 * α ^ 2 = (2 * α ^ 2 - 2) + 2 := by
      have : 2 ≤ 2 * α ^ 2 := by nlinarith
      omega
    set d : ℝ := Real.exp (Real.pi * α ^ 2 * ((t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋) ^ 2) /
        2 ^ (2 * α ^ 2 - 2) with hd
    have hBv : (c⁻¹ • (2 : ℂ) • Bc) v j = (d : ℂ) * wN l₀ := by
      have h1 : (c⁻¹ • (2 : ℂ) • Bc) v j = c⁻¹ * (2 * (((Real.exp (1 * π * α ^ 2 *
          beta s t (l₀ : ℤ) ^ 2) : ℝ) : ℂ) * M y ((t : ZMod s)⁻¹ * j))) := rfl
      have h2 : wN l₀ = (1 / 2 : ℂ) * M y ((t : ZMod s)⁻¹ * j) := by
        simp only [hwN, hl₀Z, hw₀]; rfl
      have hβ : beta s t (l₀ : ℤ) = (t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋ := by
        unfold beta rnd; push_cast; ring_nf
      have h3 : c = 2 ^ (2 * α ^ 2 - 2) * 4 := by
        rw [hc]; conv_lhs => rw [hk]
        rw [pow_add]; norm_num
      rw [h1, h2, hβ, hd, h3]
      generalize M y ((t : ZMod s)⁻¹ * j) = z
      push_cast
      field_simp
      ring
    have hd1 : |d| ≤ 1 := by
      have hb1 : |(t * l₀ : ℝ) / s - ⌊(t * l₀ : ℝ) / s + 1 / 2⌋| ≤ 1 / 2 := by
        have := abs_sub_rnd_le ((t * l₀ : ℝ) / s); unfold rnd at this; exact this
      exact d_le_one α hα _ hb1
    have hBapp : Bapprox p s t α V j.val = Dapprox p s t α Z l₀ := by
      simp only [Bapprox, psInvPerm, ZMod.natCast_zmod_val]
      rfl
    rw [hBapp, hBv]
    change ‖toC (Dapprox p s t α Z l₀) - (d : ℂ) * toC (Z l₀)‖ < 3 at hDb
    have hsplit : toC (Dapprox p s t α Z l₀) - 2 ^ p * ((d : ℂ) * wN l₀) =
        (toC (Dapprox p s t α Z l₀) - (d : ℂ) * toC (Z l₀)) + (d : ℂ) * (toC (Z l₀) - 2 ^ p * wN l₀) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h5 : |d| * ‖toC (Z l₀) - 2 ^ p * wN l₀‖ ≤ 1 * εJ :=
      mul_le_mul hd1 (hJb l₀) (norm_nonneg _) zero_le_one
    have : ((n : ℕ) : ℝ) * (10 * m + 12) + 4 = εJ + 3 := by rw [hεJ]; ring
    rw [this]; linarith


/-- Proposition 4.7 in the language of `FPApprox`: the computable maps `Sapprox` and `Bapprox`
are numerical approximations of the maps `A`, `B` of the factorisation `F_s = 2^{2α²} B F_t A`
(lifted to `ℕ`-indexed arrays). -/
theorem prop_4_7_fp (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      FPApprox p (Sapprox p s t α) (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t))
        (6 * sWidth p α + 4) ∧
      FPApprox p (Bapprox p s t α) (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s))
        (jIter p s t α * (10 * eWidth p α + 12) + 4) ∧
      SupLip (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t)) ∧
      SupLip (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s)) := by
  obtain ⟨A, B, hA, hB, hF, hSa, hBa⟩ := prop_4_7_core p s t α hst hcop hα hαp hx hp
  have hpR : (0 : ℝ) < 2 ^ p := by positivity
  have hpA' : 4 * (6 * (sWidth p α : ℝ) + 4) ≤ 2 ^ p := by exact_mod_cast hpA
  have hpB' : 100 * ((jIter p s t α : ℝ) * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p := by
    exact_mod_cast hp
  -- lifts of linear maps of norm ≤ 1 are 1-Lipschitz
  have lipA : SupLip (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t)) := by
    intro x y δ h k
    have hδ : 0 ≤ δ := (norm_nonneg _).trans (h 0)
    have e : A (fun j => x j.val) (k : ZMod t) - A (fun j => y j.val) (k : ZMod t) =
        A ((fun j : ZMod s => x j.val) - fun j => y j.val) (k : ZMod t) := by rw [map_sub]; rfl
    rw [e]
    refine (norm_le_pi_norm _ _).trans ((A.le_opNorm _).trans ?_)
    have : ‖(fun j : ZMod s => x j.val) - fun j => y j.val‖ ≤ δ :=
      (pi_norm_le_iff_of_nonneg hδ).2 (fun j => h _)
    calc ‖A‖ * _ ≤ 1 * δ := mul_le_mul (by linarith) this (norm_nonneg _) zero_le_one
      _ = δ := one_mul _
  have lipB : SupLip (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s)) := by
    intro x y δ h k
    have hδ : 0 ≤ δ := (norm_nonneg _).trans (h 0)
    have e : B (fun j => x j.val) (k : ZMod s) - B (fun j => y j.val) (k : ZMod s) =
        B ((fun j : ZMod t => x j.val) - fun j => y j.val) (k : ZMod s) := by rw [map_sub]; rfl
    rw [e]
    refine (norm_le_pi_norm _ _).trans ((B.le_opNorm _).trans ?_)
    have : ‖(fun j : ZMod t => x j.val) - fun j => y j.val‖ ≤ δ :=
      (pi_norm_le_iff_of_nonneg hδ).2 (fun j => h _)
    calc ‖B‖ * _ ≤ 1 * δ := mul_le_mul (by linarith) this (norm_nonneg _) zero_le_one
      _ = δ := one_mul _
  refine ⟨A, B, by linarith, by linarith, hF, ?_, ?_, lipA, lipB⟩
  · intro U hU
    have hu : ‖(fun j : ZMod s => gC (U j.val) / 2 ^ p)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun j => ?_)
      rw [norm_div, norm_pow, Complex.norm_two, div_le_one hpR]; exact hU _
    have herr : ∀ k : ℕ, ‖gC (Sapprox p s t α U k) - 2 ^ p *
        A (fun j => gC (U j.val) / 2 ^ p) (k : ZMod t)‖ ≤ 6 * sWidth p α + 4 := hSa U hU
    refine ⟨fun k => ?_, herr⟩
    have h1 : ‖A (fun j : ZMod s => gC (U j.val) / 2 ^ p) (k : ZMod t)‖ ≤ 11 / 20 :=
      (norm_le_pi_norm _ _).trans ((A.le_opNorm _).trans
        (by nlinarith [norm_nonneg A, norm_nonneg (fun j : ZMod s => gC (U j.val) / 2 ^ p)]))
    have h2 := norm_le_insert' (gC (Sapprox p s t α U k))
      ((2 : ℂ) ^ p * A (fun j => gC (U j.val) / 2 ^ p) (k : ZMod t))
    rw [norm_mul, norm_pow, Complex.norm_two] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 hpR.le
    linarith [herr k]
  · intro V hV
    have hv : ‖(fun k : ZMod t => gC (V k.val) / 2 ^ p)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun j => ?_)
      rw [norm_div, norm_pow, Complex.norm_two, div_le_one hpR]; exact hV _
    have herr : ∀ j : ℕ, ‖gC (Bapprox p s t α V j) - 2 ^ p *
        B (fun k => gC (V k.val) / 2 ^ p) (j : ZMod s)‖ ≤
          jIter p s t α * (10 * eWidth p α + 12) + 4 := by
      intro j
      have hj : Bapprox p s t α V j = Bapprox p s t α V ((j : ZMod s).val) := by
        simp only [Bapprox, psInvPerm, ZMod.natCast_zmod_val]
      rw [hj]; exact hBa V hV (j : ZMod s)
    refine ⟨fun j => ?_, herr⟩
    have h1 : ‖B (fun k : ZMod t => gC (V k.val) / 2 ^ p) (j : ZMod s)‖ ≤ 1 / 2 :=
      (norm_le_pi_norm _ _).trans ((B.le_opNorm _).trans
        (by nlinarith [norm_nonneg B, norm_nonneg (fun k : ZMod t => gC (V k.val) / 2 ^ p)]))
    have h2 := norm_le_insert' (gC (Bapprox p s t α V j))
      ((2 : ℂ) ^ p * B (fun k => gC (V k.val) / 2 ^ p) (j : ZMod s))
    rw [norm_mul, norm_pow, Complex.norm_two] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 hpR.le
    linarith [herr j]

end IntMul.HvdH.P47

open IntMul.HvdH in
theorem solution (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      FPApprox p (Sapprox p s t α) (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t))
        (6 * sWidth p α + 4) ∧
      FPApprox p (Bapprox p s t α) (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s))
        (jIter p s t α * (10 * eWidth p α + 12) + 4) ∧
      SupLip (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t)) ∧
      SupLip (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s)) :=  IntMul.HvdH.P47.prop_4_7_fp p s t α hst hcop hα hαp hx hp hpA
