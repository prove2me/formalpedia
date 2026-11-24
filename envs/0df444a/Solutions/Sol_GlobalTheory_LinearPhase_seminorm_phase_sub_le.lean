-- Prove2me | solution 1 for GlobalTheory.LinearPhase.seminorm_phase_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:03.533201+00:00
-- url     : https://prove2.me/submissions/59ff1190-d970-4b95-a4f2-0f25e9c358f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormLinearPhaseSecondOrderLe
import Theorems.Thm_GlobalTheory_CharFormDeriv_hasTemperateGrowth_char
import Theorems.Thm_GlobalTheory_CharFormDeriv_norm_cexp_mul_I_sub_one_le
import Theorems.Thm_GlobalTheory_CharFormDeriv_seminorm_rem_mul_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory GlobalTheory.LinearPhase
open Complex GlobalTheory.CharFormDeriv
namespace GlobalTheory.LinearPhase
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  intro V _ _ L c f k n
  set L' : V →L[ℝ] ℝ := (-(2 * Real.pi)) • L with hL'
  have hL'x : ∀ x, ((L' x : ℝ) : ℂ) = -(2 * Real.pi) * (L x : ℂ) := fun x => by
    simp [hL']
  set K := 3 * 2 ^ n * (1 + ‖L'‖) ^ (n + 2) *
      (2 ^ (k + 2) * ((Finset.Iic (k + 2, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)
      with hK
  have hgt : Function.HasTemperateGrowth (fun x : V => ((L x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp L).hasTemperateGrowth
  set g : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f with hgdef
  have hg : ∀ x, g x = (L x : ℂ) * f x := fun x => by
    rw [hgdef, SchwartzMap.smulLeftCLM_apply_apply hgt, smul_eq_mul]
  refine ⟨K + 2 * |2 * Real.pi * c| *
    (SchwartzMap.seminorm ℂ k n f + 2 * Real.pi * SchwartzMap.seminorm ℂ k n g), fun t ht1 => ?_⟩
  set a : ℂ := Complex.exp (((-(2 * Real.pi * c * t ^ 2) : ℝ) : ℂ) * I) with ha
  have hfun : (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) := by
    funext x
    rw [ha, ← Complex.exp_add, hL'x]
    congr 1
    push_cast
    ring
  have het : Function.HasTemperateGrowth fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ)) :=
    (Function.HasTemperateGrowth.const a).mul (hasTemperateGrowth_char L' t)
  rw [hfun]
  set A : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => Complex.exp ((I * t) * (L' x : ℂ))) f with hAdef
  have hA : ∀ x, A x = Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hAdef, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_char L' t), smul_eq_mul]
  set E : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : V => a * Complex.exp ((I * t) * (L' x : ℂ))) f with hEdef
  have hE : ∀ x, E x = a * Complex.exp ((I * t) * (L' x : ℂ)) * f x := fun x => by
    rw [hEdef, SchwartzMap.smulLeftCLM_apply_apply het, smul_eq_mul]
  rcases eq_or_ne t 0 with ht0 | ht0
  · have h0 : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g = 0 := by
      ext x
      simp only [SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hE, ha, ht0]
      simp
    rw [h0, map_zero, ht0]
    simp
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  set u : 𝓢(V, ℂ) := (t : ℂ)⁻¹ • (A - f) + (2 * Real.pi * I : ℂ) • g with hudef
  have hu : ∀ x, u x = rem t (L' x) * f x := fun x => by
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hg,
      rem, smul_eq_mul, hL'x]
    ring
  have hub : SchwartzMap.seminorm ℂ k n u ≤ |t| * K := seminorm_rem_mul_le L' f u ht0 ht1 hu k n
  have hid : E - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • g
      = (a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g) := by
    ext x
    simp only [hudef, SchwartzMap.add_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, hA, hE,
      smul_eq_mul]
    field_simp
    ring
  have hna : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hna1 : ‖a - 1‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 := by
    refine (norm_cexp_mul_I_sub_one_le _).trans (le_of_eq ?_)
    rw [abs_neg, abs_mul (2 * Real.pi * c), abs_of_nonneg (sq_nonneg t)]
    ring
  have hpf := apply_nonneg (SchwartzMap.seminorm ℂ k n) f
  have hpg := apply_nonneg (SchwartzMap.seminorm ℂ k n) g
  have hpi := Real.pi_pos
  have hn1 : ‖a * t‖ = |t| := by rw [norm_mul, hna, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖-((a - 1) * t * (2 * Real.pi * I))‖ ≤ 2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) := by
    have h2 : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [norm_neg, norm_mul, norm_mul, h2, Complex.norm_real, Real.norm_eq_abs]
    calc ‖a - 1‖ * |t| * (2 * Real.pi) ≤ (2 * |2 * Real.pi * c| * t ^ 2) * 1 * (2 * Real.pi) := by
          gcongr
      _ = _ := by ring
  rw [hid]
  calc SchwartzMap.seminorm ℂ k n ((a * t) • u + ((a - 1) • f + (-((a - 1) * t * (2 * Real.pi * I))) • g))
      ≤ SchwartzMap.seminorm ℂ k n ((a * t) • u) + (SchwartzMap.seminorm ℂ k n ((a - 1) • f) +
          SchwartzMap.seminorm ℂ k n ((-((a - 1) * t * (2 * Real.pi * I))) • g)) :=
        (map_add_le_add _ _ _).trans (by gcongr; exact map_add_le_add _ _ _)
    _ = |t| * SchwartzMap.seminorm ℂ k n u + (‖a - 1‖ * SchwartzMap.seminorm ℂ k n f +
          ‖-((a - 1) * t * (2 * Real.pi * I))‖ * SchwartzMap.seminorm ℂ k n g) := by
        rw [map_smul_eq_mul, map_smul_eq_mul, map_smul_eq_mul, hn1]
    _ ≤ |t| * (|t| * K) + (2 * |2 * Real.pi * c| * t ^ 2 * SchwartzMap.seminorm ℂ k n f +
          2 * |2 * Real.pi * c| * t ^ 2 * (2 * Real.pi) * SchwartzMap.seminorm ℂ k n g) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← sq, sq_abs]; ring
end GlobalTheory.LinearPhase
