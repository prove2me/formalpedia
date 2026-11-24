-- Prove2me | solution 1 for GlobalTheory.isAlgebraic_embedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:21.424043+00:00
-- url     : https://prove2.me/submissions/02895410-abad-40fb-bba5-4565314768cf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic

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
open GlobalTheory
open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
namespace GlobalTheory
theorem _root_.solution {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
end GlobalTheory
