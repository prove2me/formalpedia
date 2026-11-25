-- Prove2me | solution 1 for GlobalTheory.HeckeLocDec.loc_div_val_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:26.57292+00:00
-- url     : https://prove2.me/submissions/693afd60-c256-4bc4-9726-a60ee18abcd4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharLocalValueDivUniformiserPow
import Theorems.Thm_GlobalTheory_HeckeLocDec_localIdele_unitPart_mem
import Theorems.Thm_PI_AlgValsFin_W_torsUnits


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
theorem _root_.solution (L : Type) [Field L] [NumberField L] (χ : HChar L) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ),
      ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  obtain ⟨N, hN, hT⟩ := PI.AlgValsFin.W.torsUnits L χ
  refine ⟨N, hN, fun w x => ?_⟩
  have hx0 : Valued.v (x : w.adicCompletion L) ≠ 0 := by simp
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v (x : w.adicCompletion L) = WithZero.exp (-a) :=
    ⟨-WithZero.log (Valued.v (x : w.adicCompletion L)), by rw [neg_neg, WithZero.exp_log hx0]⟩
  refine ⟨a, ?_⟩
  have hmem := localIdele_unitPart_mem L w x a ha
  have h := hT _ hmem
  have e : χ.loc w x / χ.val w ^ a = χ.1 (localIdele L w (x * (atFin w (unif w)) ^ (-a))) := by
    show χ.loc w x / χ.loc w (atFin w (unif w)) ^ a = χ.loc w (x * (atFin w (unif w)) ^ (-a))
    rw [map_mul, map_zpow, zpow_neg, div_eq_mul_inv]
  rw [e, ← Units.val_pow_eq_pow_val, h, Units.val_one]
end GlobalTheory.HeckeLocDec
