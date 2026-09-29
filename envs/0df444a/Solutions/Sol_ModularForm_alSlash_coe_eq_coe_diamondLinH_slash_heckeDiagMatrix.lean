-- Prove2me | solution 1 for ModularForm.alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5e01f9ff-92e7-510a-b64c-7245f3036537

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix

set_option autoImplicit false

open ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem solution {M p : ℕ} [NeZero M] (hp : p.Prime) (W : ModularForm.AtkinLehnerDatum M p) [NeZero W.R]
    (H' : Subgroup (ZMod W.R)ˣ) (k : ℤ) (G : CuspForm (CohCarrier.GammaH W.R H') k) (d₀ : (ZMod W.R)ˣ)
    (hd₀ : (d₀ : ZMod W.R) = (p : ZMod W.R)) :
    ModularForm.alSlash W k ⇑G = (⇑(CuspForm.diamondLinH k d₀ G)) ∣[k] ModularForm.heckeDiagMatrix p := by

  have hdet : (!![W.a, W.b; (W.R : ℤ), (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination W.bezout
  set σ : SL(2, ℤ) := ⟨!![W.a, W.b; (W.R : ℤ), (p : ℤ)], hdet⟩ with hσdef
  have hσ0 : σ ∈ Gamma0 W.R := by
    rw [Gamma0_mem]
    show (((!![W.a, W.b; (W.R : ℤ), (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod W.R) = 0
    simp
  have hσu : CohCarrier.gamma0Units W.R ⟨σ, hσ0⟩ = d₀ := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, hd₀]
    show (((!![W.a, W.b; (W.R : ℤ), (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) = (p : ZMod W.R)
    simp

  have hW : W.alGL = (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p := by
    apply Units.ext
    rw [Units.val_mul, ModularForm.val_heckeDiagMatrix hp.ne_zero, AtkinLehnerDatum.alGL_coe, AtkinLehnerDatum.mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL, hσdef, mul_comm]
  rw [ModularForm.alSlash_def, hW, SlashAction.slash_mul,
    CuspForm.coe_diamondLinH_eq_slash k (CuspForm.stableD W.R H' k) d₀ ⟨σ, hσ0⟩ hσu G]

end S_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
end P2MW
export P2MW.S_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix (solution)
