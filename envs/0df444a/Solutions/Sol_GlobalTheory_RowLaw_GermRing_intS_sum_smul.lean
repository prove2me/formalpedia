-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.intS_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:10.282097+00:00
-- url     : https://prove2.me/submissions/93ff42cb-de3d-4a4e-99e7-617ec0fee985

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution {V : VF C} {σ ι : Type} [Fintype ι] {w : ι → C} (hw : ∀ i, V.Ge 0 (w i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, IntS V (f i)) : IntS V (∑ i, w i • f i) := fun μ => by
  rw [map_sum]
  exact VF.Ge.sum fun i _ => by rw [map_smul, smul_eq_mul]; exact (hw i).mul_int (hf i μ)
end GlobalTheory.RowLaw.GermRing
