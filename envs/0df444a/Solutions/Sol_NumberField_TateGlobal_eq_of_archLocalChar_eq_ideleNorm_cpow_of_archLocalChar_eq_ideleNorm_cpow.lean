-- Prove2me | solution 1 for NumberField.TateGlobal.eq_of_archLocalChar_eq_ideleNorm_cpow_of_archLocalChar_eq_ideleNorm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a90276c3-8fb4-5801-9a5a-c4fbead2fd1c

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_eq_of_archLocalChar_eq_ideleNorm_cpow_of_archLocalChar_eq_ideleNorm_cpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

namespace WsB
namespace L4

p2m_open "NumberField.InfinitePlace.Completion"

variable (K : Type) [Field K] [NumberField K]

theorem norm_ext (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem exists_unit_of_rat (v : InfinitePlace K) (q : ℚ) (hq : 0 < q) :
    ∃ x : (v.Completion)ˣ, extensionEmbedding v (x : v.Completion) = ((q : ℝ) : ℂ) ∧ ‖(x : v.Completion)‖ = q := by
  set xK : WithAbs v.1 := (q : WithAbs v.1) with hxK
  set y : v.Completion := (xK : v.Completion) with hy
  have hemb : extensionEmbedding v y = ((q : ℝ) : ℂ) := by
    rw [hy, extensionEmbedding_coe, hxK, map_ratCast, map_ratCast]
    norm_cast
  have hnorm : ‖y‖ = q := by
    rw [← norm_ext, hemb]; simp [abs_of_pos hq, hq.le]
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact absurd hnorm (by exact_mod_cast hq.ne)
  exact ⟨Units.mk0 y hy0, hemb, hnorm⟩

theorem main (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : InfinitePlace K) (τ τ' : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (extensionEmbedding v (x : v.Completion)).re →
      (extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (hτ' : ∀ x : (v.Completion)ˣ,
      0 < (extensionEmbedding v (x : v.Completion)).re →
      (extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ' : ℝ) : ℂ) * Complex.I)) :
    τ = τ' := by

  have key : ∀ q : ℚ, 0 < q → ∃ k : ℤ, (v.mult : ℝ) * Real.log q * (τ - τ') = k * (2 * Real.pi) := by
    intro q hq
    obtain ⟨x, hemb, hnorm⟩ := exists_unit_of_rat K v q hq
    have hre : 0 < (extensionEmbedding v (x : v.Completion)).re := by rw [hemb]; simpa using hq
    have him : (extensionEmbedding v (x : v.Completion)).im = 0 := by rw [hemb]; simp
    have h := (hτ x hre him).symm.trans (hτ' x hre him)
    rw [ideleNorm_archUnitHom, hnorm] at h
    have hN : (0 : ℝ) < (q : ℝ) ^ v.mult := pow_pos (by exact_mod_cast hq) _
    have hN' : (((q : ℝ) ^ v.mult : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Complex.cpow_def_of_ne_zero hN', Complex.cpow_def_of_ne_zero hN', Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have hlog : Complex.log (((q : ℝ) ^ v.mult : ℝ) : ℂ) = ((Real.log ((q : ℝ) ^ v.mult) : ℝ) : ℂ) :=
      (Complex.ofReal_log hN.le).symm
    rw [hlog, Real.log_pow] at hk
    have := congrArg Complex.im hk
    push_cast at this
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im, Complex.intCast_re, Complex.intCast_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, add_zero, sub_zero, mul_one, zero_add] at this
    linarith
  by_contra hne
  have hΔ : τ - τ' ≠ 0 := sub_ne_zero.mpr hne

  set n : ℕ := ⌊(v.mult : ℝ) * |τ - τ'|⌋₊ + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
  have hnbig : (v.mult : ℝ) * |τ - τ'| < n := by
    rw [hn]; push_cast; exact Nat.lt_floor_add_one _
  set q : ℚ := 1 + 1 / (n : ℚ) with hq
  have hqR : (q : ℝ) = 1 + 1 / (n : ℝ) := by rw [hq]; push_cast; rfl
  have hq1 : (1 : ℝ) < (q : ℝ) := by
    rw [hqR]; have : (0:ℝ) < 1 / (n:ℝ) := by positivity
    linarith
  have hqpos : 0 < q := by exact_mod_cast (lt_trans zero_lt_one hq1)
  obtain ⟨k, hk⟩ := key q hqpos
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlogle : Real.log (q : ℝ) ≤ 1 / (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hq1)
    rw [hqR] at this ⊢; linarith

  have hbound : |(v.mult : ℝ) * Real.log q * (τ - τ')| < 2 * Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos hlogpos, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (v.mult : ℝ) * Real.log q * |τ - τ'| ≤ (v.mult : ℝ) * (1 / n) * |τ - τ'| := by
          gcongr
      _ = ((v.mult : ℝ) * |τ - τ'|) / n := by ring
      _ < 1 := by rw [div_lt_one hnpos]; exact hnbig
      _ < 2 * Real.pi := by have := Real.pi_gt_three; linarith
  rw [hk, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
  have hk0 : k = 0 := by
    have h1 : |(k : ℝ)| < 1 := by
      by_contra h; push_neg at h
      have := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 2 * Real.pi)
      linarith
    have h2 : |k| < 1 := by exact_mod_cast h1
    rcases abs_lt.mp h2 with ⟨h3, h4⟩
    omega
  rw [hk0, Int.cast_zero, zero_mul] at hk
  have hm0 : (v.mult : ℝ) ≠ 0 := InfinitePlace.mult_coe_ne_zero
  rcases mul_eq_zero.mp hk with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hm0 h
    · exact absurd h hlogpos.ne'
  · exact hΔ h

end WsB.L4

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : InfinitePlace K) (τ τ' : ℝ)
    (hτ : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I))
    (hτ' : ∀ x : (v.Completion)ˣ,
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ' : ℝ) : ℂ) * Complex.I)) :
    τ = τ' :=
  WsB.L4.main K χ v τ τ' hτ hτ'

end S_NumberField_TateGlobal_eq_of_archLocalChar_eq_ideleNorm_cpow_of_archLocalChar_eq_ideleNorm_cpow
end P2MW
export P2MW.S_NumberField_TateGlobal_eq_of_archLocalChar_eq_ideleNorm_cpow_of_archLocalChar_eq_ideleNorm_cpow (solution)
