-- Prove2me | solution 1 for ModularCurve.qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/32cd4e92-58ba-5095-9d00-95dde5f70c06

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hNℓ : ((N * ℓ : ℕ) : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ModularCurve.qExpand K ℓ (ModularCurve.jqModC K) ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) := by
  set Γ' : Subgroup SL(2, ℤ) := CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ) with hΓ'

  have hcond : ∀ γ ∈ Γ', ∃ γ₁ ∈ (⊤ : Subgroup SL(2, ℤ)),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
    intro γ hγ
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 (N * ℓ) := hγ.2
    rw [CongruenceSubgroup.Gamma0_mem] at hγ0
    have hdvd : ((N * ℓ : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ0
    have hℓc : (ℓ : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr (dvd_mul_left ℓ N)).trans (by exact_mod_cast hdvd)
    obtain ⟨c', hc'⟩ := hℓc
    have hdet : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
      have := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
      rw [γ.det_coe] at this
      linarith [this]
    refine ⟨⟨!![γ 0 0, (ℓ : ℤ) * γ 0 1; c', γ 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      rw [hc'] at hdet
      linear_combination hdet
    · rfl
    · rfl
    · show (ℓ : ℤ) * c' = γ 1 0
      rw [hc']
    · rfl
  have hj : ModularCurve.jqModC K ∈ ModularCurve.intFormRatiosC K (⊤ : Subgroup SL(2, ℤ)) :=
    ModularCurve.jqModC_mem_intFormRatiosC K ⊤
  have himg := ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := ⊤) (Γ' := Γ')
    (Subgroup.mem_top _) ℓ hcond
  exact ModularCurve.intFormRatiosC_subset K Γ' (himg ⟨_, hj, rfl⟩)

end S_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul (solution)
