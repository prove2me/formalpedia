-- Prove2me | solution 1 for ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/14ce9729-f5e0-5fc0-a7d5-d1f8075e28fb

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffEmb coeffEmb_coeff jqModC jqNModC jqModC_rat map_jqModC exists_gamma0_qExpansion_div_eq_jqNModC"
namespace JqdRatioOfLevel
p2m_open "ModularCurve"

theorem coeffEmb_qExpand_eq (d : ℕ) [NeZero d] (x : LaurentSeries ℚ) :
    coeffEmb ℂ (qExpand ℚ d x) = qExpand ℂ d (coeffEmb ℂ x) := by
  ext k
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd (hk := hk), qExpand_coeff_of_not_dvd (hk := hk),
      map_zero]

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_qExpand_jq_eq (d : ℕ) [NeZero d] :
    coeffEmb ℂ (qExpand ℚ d jq) = jqNModC ℂ d := by
  rw [coeffEmb_qExpand_eq, coeffEmb_jq_eq]
  rfl

theorem Gamma0_le_of_dvd {d N : ℕ} (hd : d ∣ N) :
    CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 d := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr hd).trans hA

theorem Gamma0GL_le_of_dvd {d N : ℕ} (hd : d ∣ N) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 d : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le_of_dvd hd)

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn f γ (hle hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono hle)

@[scoped simp]
theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) : ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

theorem restrict_ne_zero {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    {f : ModularForm Γ k} (hf : f ≠ 0) : restrict hle f ≠ 0 := by
  intro h
  apply hf
  apply DFunLike.ext
  intro z
  have := congrArg (fun g : ModularForm Γ' k => (g : ℍ → ℂ) z) h
  simpa using this

theorem one_mem_strictPeriods (d : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qExpansion_coe_ne_zero {d : ℕ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 d) k)
    (hf : f ≠ 0) : ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods d)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa using h

end ModularCurve.JqdRatioOfLevel
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel"
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel"

open UpperHalfPlane in
open ModularCurve.JqdRatioOfLevel in
theorem solution (N d : ℕ)
    [NeZero N] [NeZero d] (hd : d ∣ N) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ d ModularCurve.jq) *
          ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  obtain ⟨G, H, hH, hdiv⟩ := ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC d
  have hle := Gamma0GL_le_of_dvd hd
  refine ⟨12, restrict hle G, restrict hle H, restrict_ne_zero hle hH, ?_⟩
  rw [coe_restrict, coe_restrict, ModularCurve.JqdRatioOfLevel.coeffEmb_qExpand_jq_eq, ← hdiv]
  exact div_mul_cancel₀ _ (qExpansion_coe_ne_zero H hH)

end S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq (solution)
