-- Prove2me | solution 1 for ModularForm.logEta_modular_S_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f7d64e8e-0342-580d-88fa-63b377ce9d14

import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.RCLike.Sqrt
import Theorems.Thm_ModularForm_eta_modular_S_smul
import Theorems.Thm_ModularForm_exp_logEta
import Theorems.Thm_ModularForm_continuous_logEta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_logEta_modular_S_smul

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

private theorem _root_.DedekindEtaLog.exp_logEta (z : ℍ) : exp (logEta z) = η (z : ℂ) := ModularForm.exp_logEta z

p2m_export "DedekindEtaLog" "exp_logEta"
private theorem _root_.DedekindEtaLog.continuous_logEta : Continuous fun τ : ℍ => logEta τ := ModularForm.continuous_logEta

p2m_export "DedekindEtaLog" "continuous_logEta"
lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [modular_S_smul]; simp [inv_neg]

lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, UpperHalfPlane.coe_I, Complex.inv_I, neg_neg]

lemma neg_I_mul_re (ζ : ℂ) : (-I * ζ).re = ζ.im := by simp

lemma continuous_sl_smul (γ : SL(2, ℤ)) : Continuous fun τ : ℍ => γ • τ := by
  have : (fun τ : ℍ => γ • τ) = fun τ : ℍ => (γ : GL (Fin 2) ℝ) • τ := funext fun τ => ModularGroup.sl_moeb γ τ
  rw [this]
  exact continuous_const_smul _

theorem eq_of_exp_eq_one {f : ℍ → ℂ} (hf : Continuous f) (h1 : ∀ τ, exp (f τ) = 1) (τ : ℍ) :
    f τ = f UpperHalfPlane.I := by
  have hmaps : Set.MapsTo f Set.univ (AddSubgroup.zmultiples (2 * π * I) : Set ℂ) := by
    intro τ _
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 (h1 τ)
    rw [hn, SetLike.mem_coe, ← zsmul_eq_mul]
    exact zsmul_mem (AddSubgroup.mem_zmultiples _) n
  have hT : IsDiscrete (AddSubgroup.zmultiples (2 * π * I) : Set ℂ) :=
    isDiscrete_iff_discreteTopology.2 (inferInstanceAs (DiscreteTopology (AddSubgroup.zmultiples (2 * π * I))))
  exact isPreconnected_univ.constant_of_mapsTo hT hf.continuousOn hmaps (Set.mem_univ _) (Set.mem_univ _)

theorem logEta_S_smul (z : ℍ) :
    logEta ((ModularGroup.S • z : ℍ) : ℂ) = logEta z + log (-I * z) / 2 := by
  let D : ℍ → ℂ := fun z => logEta ((ModularGroup.S • z : ℍ) : ℂ) - logEta z - log (-I * z) / 2
  have hD : Continuous D := by
    refine ((continuous_logEta.comp (continuous_sl_smul ModularGroup.S)).sub continuous_logEta).sub ?_
    refine Continuous.div_const (continuous_iff_continuousAt.2 fun τ => ?_) 2
    have hc : Continuous fun τ : ℍ => -I * (τ : ℂ) := by fun_prop
    exact hc.continuousAt.clog (Or.inl (by rw [neg_I_mul_re, UpperHalfPlane.coe_im]; exact τ.im_pos))
  have h1 : ∀ τ, exp (D τ) = 1 := by
    intro τ
    have hτ0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) (UpperHalfPlane.ne_zero τ)
    have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
    have hs : Complex.sqrt (-I * τ) ≠ 0 := by
      rw [sqrt_eq_exp hτ0]; exact exp_ne_zero _
    have e1 : exp (logEta ((ModularGroup.S • τ : ℍ) : ℂ)) = Complex.sqrt (-I * τ) * η (τ : ℂ) := by
      rw [exp_logEta, ModularForm.eta_modular_S_smul τ]
    have e2 : exp (log (-I * τ) / 2) = Complex.sqrt (-I * τ) := (sqrt_eq_exp hτ0).symm
    show exp (logEta ((ModularGroup.S • τ : ℍ) : ℂ) - logEta τ - log (-I * τ) / 2) = 1
    rw [exp_sub, exp_sub, e1, exp_logEta, e2, mul_div_cancel_right₀ _ hη, div_self hs]
  have h := eq_of_exp_eq_one hD h1 z
  have h0 : D UpperHalfPlane.I = 0 := by
    simp only [D, S_smul_I, UpperHalfPlane.coe_I, sub_self, zero_sub, neg_eq_zero]
    rw [show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], log_one, zero_div]
  have : D z = 0 := h.trans h0
  simp only [D] at this
  linear_combination this

end DedekindEtaLog

end

theorem solution (z : UpperHalfPlane) : (Real.pi * Complex.I * ((ModularGroup.S • z : UpperHalfPlane) : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n ((ModularGroup.S • z : UpperHalfPlane) : ℂ))) = (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) + Complex.log (-Complex.I * z) / 2 :=
  DedekindEtaLog.logEta_S_smul z

end S_ModularForm_logEta_modular_S_smul
end P2MW
export P2MW.S_ModularForm_logEta_modular_S_smul (solution)
