-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.intS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:50.154041+00:00
-- url     : https://prove2.me/submissions/b18589fa-1ece-4689-a154-60ae7c51126a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsInDeg
import Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsInDeg


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
theorem _root_.solution {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (h0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f) :
    IntS V (subst a f) := fun μ =>
  mem_coeffsInDeg.1 (subst_mem_coeffsInDeg (S := intRing V) (g := μ.degree + 1) h0
    (fun s => mem_coeffsInDeg.2 fun d _ => ha s d) (mem_coeffsInDeg.2 fun d _ => hf d)) μ (Nat.lt_succ_self _)
end GlobalTheory.RowLaw.GermRing
