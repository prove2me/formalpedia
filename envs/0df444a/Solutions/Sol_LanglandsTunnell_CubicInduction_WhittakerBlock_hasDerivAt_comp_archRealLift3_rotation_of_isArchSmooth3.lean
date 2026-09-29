-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8509b86b-a79a-53be-b452-30b0411a1176

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock

namespace RotAux

def I₃ : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then 1 else 0

def E (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

theorem det_I₃_ne : (Matrix.of I₃).det ≠ 0 := by
  have : (Matrix.of I₃ : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    ext i j; simp [I₃, Matrix.one_apply]
  rw [this, Matrix.det_one]; exact one_ne_zero

theorem isOpen_det_ne : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem rot_entry_eq (c₁ c₂ : Fin 3) (s : ℝ) (i j : Fin 3) :
    (if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
        if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
        if i = j then 1 else 0) =
      (I₃ + ((Real.cos s - 1) • (E c₁ c₁ + E c₂ c₂ - E c₁ c₁ * E c₂ c₂) + Real.sin s • (E c₂ c₁ - E c₁ c₂))) i j := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, I₃, E]
  fin_cases c₁ <;> fin_cases c₂ <;> fin_cases i <;> fin_cases j <;> simp

theorem exists_fderiv_of_isArchSmooth3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ L : (Fin 3 → Fin 3 → ℝ) →L[ℝ] ℂ,
      (∀ (γ : ℝ → Fin 3 → Fin 3 → ℝ) (γ' : Fin 3 → Fin 3 → ℝ), γ 0 = I₃ → HasDerivAt γ γ' 0 →
        HasDerivAt (fun s => φ (g * WhittakerBlock.archRealLift3 (γ s))) (L γ') 0) ∧
      ∀ i j : Fin 3, archDeriv i j φ g = L (E i j) := by
  let Φ : (Fin 3 → Fin 3 → ℝ) → ℂ := fun e => φ (g * WhittakerBlock.archRealLift3 e)
  have hd : DifferentiableAt ℝ Φ I₃ :=
    ((hφ g).differentiableOn (by simp)).differentiableAt (isOpen_det_ne.mem_nhds det_I₃_ne)
  refine ⟨fderiv ℝ Φ I₃, fun γ γ' h0 hγ => ?_, fun i j => ?_⟩
  · have h : HasFDerivAt Φ (fderiv ℝ Φ I₃) (γ 0) := by rw [h0]; exact hd.hasFDerivAt
    have h2 := h.comp_hasDerivAt 0 hγ
    exact h2
  · have hγ : HasDerivAt (fun s : ℝ => fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)
        (E i j) 0 := by
      refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
      show HasDerivAt (fun s : ℝ => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) (E i j a b) 0
      simp only [E]
      by_cases hab : a = i ∧ b = j
      · simp only [hab, and_self, if_true]
        exact (hasDerivAt_id 0).const_add _
      · simp only [hab, if_false, add_zero]
        exact hasDerivAt_const 0 _
    have h0 : (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then (0 : ℝ) else 0) = I₃ := by
      funext a b; simp [I₃]
    have h : HasFDerivAt Φ (fderiv ℝ Φ I₃)
        (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then (0 : ℝ) else 0) := by
      rw [h0]; exact hd.hasFDerivAt
    have h2 := (h.comp_hasDerivAt 0 hγ).deriv
    exact h2

end RotAux

open RotAux in
theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (c₁ c₂ : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    HasDerivAt
      (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (fun i j =>
        if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
        if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
        if i = j then 1 else 0)))
      (archDeriv c₂ c₁ φ g - archDeriv c₁ c₂ φ g) 0 := by
  obtain ⟨L, hL, hLE⟩ := exists_fderiv_of_isArchSmooth3 φ hφ g

  let D : Fin 3 → Fin 3 → ℝ := E c₁ c₁ + E c₂ c₂ - E c₁ c₁ * E c₂ c₂
  let R : Fin 3 → Fin 3 → ℝ := E c₂ c₁ - E c₁ c₂
  let γ : ℝ → Fin 3 → Fin 3 → ℝ := fun s => I₃ + ((Real.cos s - 1) • D + Real.sin s • R)
  have hγ0 : γ 0 = I₃ := by
    show I₃ + ((Real.cos 0 - 1) • D + Real.sin 0 • R) = I₃
    rw [Real.cos_zero, sub_self, zero_smul, Real.sin_zero, zero_smul, add_zero, add_zero]
  have hγ : HasDerivAt γ R 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (Real.cos s - 1) • D) ((-Real.sin 0) • D) 0 :=
      ((Real.hasDerivAt_cos 0).sub_const 1).smul_const D
    have h2 : HasDerivAt (fun s : ℝ => Real.sin s • R) (Real.cos 0 • R) 0 :=
      (Real.hasDerivAt_sin 0).smul_const R
    have h := (h1.add h2).const_add I₃
    rw [Real.sin_zero, neg_zero, zero_smul, Real.cos_zero, one_smul, zero_add] at h
    exact h
  have h := hL γ R hγ0 hγ
  have hfun : (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (fun i j =>
        if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
        if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
        if i = j then 1 else 0))) = fun s => φ (g * WhittakerBlock.archRealLift3 (γ s)) := by
    funext s
    have hs : (fun i j : Fin 3 =>
        if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
        if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
        if i = j then (1 : ℝ) else 0) = γ s := funext fun i => funext fun j => rot_entry_eq c₁ c₂ s i j
    rw [hs]
  rw [hfun, hLE, hLE, ← map_sub]
  exact h

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3 (solution)
