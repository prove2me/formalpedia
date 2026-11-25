-- Prove2me | solution 1 for GlobalTheory.CMVal.finPart_eq_val_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:17.614031+00:00
-- url     : https://prove2.me/submissions/89b6bba0-1287-472d-9fda-f4e40a07b5f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_SuppAt_finPart_eq
import Theorems.Thm_Formalism_L2_Host_unif_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable {I : Type} [Fintype I]
namespace GlobalTheory.CMVal
theorem _root_.solution {χ : HChar E} {v : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt v) {y : (Af E)ˣ} (hy : SuppAt v y)
    {n : ℤ} (hn : Valued.v ((y : Af E) v) = WithZero.exp (-n)) : finPart χ y = χ.val v ^ n := by
  have hu : IsUnitAt v (coord v y * (atFin v (unif v) ^ n)⁻¹) := by
    have h2 := unif_spec v
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, coe_coord, hn, h2,
      ← WithZero.exp_zsmul]
    simp
  have h3 := h _ hu
  rw [map_mul, map_inv, mul_inv_eq_one, map_zpow] at h3
  rw [hy.finPart_eq, h3]
  rfl
end GlobalTheory.CMVal
