-- Prove2me | solution 1 for ModularCurve.qExpand_jqModC_mem_intFormRatiosC_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fc4abe5f-96c3-58d7-a48a-ec299d2987b8

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve HahnSeries
open scoped MatrixGroups

namespace JGen

theorem exists_conj_of_mem_gammaH (N N' : ℕ) [NeZero N] [NeZero N'] (hN' : N' ∣ N) (H : Subgroup (ZMod N)ˣ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH N H) :
    ∃ γ₀ ∈ (⊤ : Subgroup SL(2, ℤ)),
      ((γ₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ∧
      ((γ₀ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (N' : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ∧
      ((N' : ℤ) * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ∧
      ((γ₀ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := CohCarrier.GammaH_le_Gamma0 (M := N) H hγ
  have hc : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := by
    simpa using (CongruenceSubgroup.Gamma0_mem).mp h0
  have hdvdN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hc
  have hdvd : (N' : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (Int.natCast_dvd_natCast.mpr hN').trans hdvdN
  obtain ⟨c, hcdef⟩ := hdvd
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (N' : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hcdef] at hdet
    linear_combination hdet
  · rfl
  · rfl
  · show (N' : ℤ) * c = _
    rw [hcdef]
  · rfl

end JGen

theorem solution
    (K : Type*) [Field K] (N N' : ℕ) [NeZero N] [NeZero N'] (hN' : N' ∣ N) (H : Subgroup (ZMod N)ˣ) :
    qExpand K N' (jqModC K) ∈ intFormRatiosC K (CohCarrier.GammaH N H) :=
  qExpand_image_intFormRatiosC_subset K (Γ := ⊤) (Γ' := CohCarrier.GammaH N H) (Subgroup.mem_top _) N'
    (fun γ hγ => JGen.exists_conj_of_mem_gammaH N N' hN' H γ hγ)
    ⟨jqModC K, jqModC_mem_intFormRatiosC K ⊤, rfl⟩

end S_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH
end P2MW
export P2MW.S_ModularCurve_qExpand_jqModC_mem_intFormRatiosC_gammaH (solution)
