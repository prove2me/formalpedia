-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.upG_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:15:36.48453+00:00
-- url     : https://prove2.me/submissions/bc5d34d2-67b5-4a22-87e4-6042cae8c0ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution (g : Fin 2) {σ : Type} [Finite σ] {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (subst a f) = subst (fun s => upG g (a s)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha)
    (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) f
end GlobalTheory.RowLaw.GermRing
