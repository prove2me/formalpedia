-- Prove2me | solution 1 for GlobalTheory.CMVal.levelLe_iff_finPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:42.847391+00:00
-- url     : https://prove2.me/submissions/e8495832-0ac3-46ef-93d6-d2aba76b7e11

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single
import Theorems.Thm_GlobalTheory_CMVal_finPart_single
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
theorem _root_.solution (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ ∀ y : (Af E)ˣ, SuppAt v y → Valued.v ((y : Af E) v) = 1 →
      Valued.v ((y : Af E) v - 1) ≤ WithZero.exp (-(n : ℤ)) → finPart χ y = 1 := by
  constructor
  · intro h y hy h1 h2
    rw [hy.finPart_eq]
    exact h _ h1 h2
  · intro h x hx hx'
    rw [← finPart_single]
    exact h _ (suppAt_single v x) (by rw [single_self]; exact hx) (by rw [single_self]; exact hx')
end GlobalTheory.CMVal
