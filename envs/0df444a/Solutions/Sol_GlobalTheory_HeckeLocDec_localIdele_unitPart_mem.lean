-- Prove2me | solution 1 for GlobalTheory.HeckeLocDec.localIdele_unitPart_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:39.028222+00:00
-- url     : https://prove2.me/submissions/6b7b7022-be07-40b3-98f9-a389a4bb23bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharLocalValueDivUniformiserPow
import Theorems.Thm_Formalism_L2_Host_unif_spec
import Theorems.Thm_Neutral_B1_localIdele_isSupportedAt
import Theorems.Thm_PI_AlgValsFin_W_evF_localIdele_ne
import Theorems.Thm_PI_AlgValsFin_W_evF_localIdele_self
import Theorems.Thm_PI_AlgValsFin_W_evF_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory GlobalTheory.HeckeLocDec
namespace GlobalTheory.HeckeLocDec
theorem _root_.solution (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) (a : ℤ) (ha : Valued.v (x : w.adicCompletion L) = WithZero.exp (-a)) :
    localIdele L w (x * (atFin w (unif w)) ^ (-a)) ∈ PI.AlgValsFin.W.UFin L := by
  refine ⟨?_, fun w' => ?_⟩
  · funext v
    exact (localIdele_isSupportedAt L w _).1 v
  · by_cases h : w' = w
    · subst h
      rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_self]
      have h1 : Valued.v ((atFin w' (unif w') : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
          WithZero.exp (-1) := unif_spec w'
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, ha,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_ne w' w h]
      simp
end GlobalTheory.HeckeLocDec
