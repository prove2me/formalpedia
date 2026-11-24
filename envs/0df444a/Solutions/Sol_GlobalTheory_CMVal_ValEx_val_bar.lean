-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.val_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:10.249839+00:00
-- url     : https://prove2.me/submissions/c5f0f631-e5f8-447f-9368-f6cc67224903

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_QNorm_valuation_of_eq_comap


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
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
local notation "cc" => IsCMField.complexConj E
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) (y : E) : (bar w).valuation E y = w.valuation E ((cc).toRingEquiv y) :=
  GlobalTheory.QNorm.valuation_of_eq_comap _ w _ rfl y
end GlobalTheory.CMVal.ValEx
