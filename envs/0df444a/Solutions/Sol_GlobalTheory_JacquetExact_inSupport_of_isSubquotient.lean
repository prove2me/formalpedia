-- Prove2me | solution 1 for GlobalTheory.JacquetExact.inSupport_of_isSubquotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:43.120388+00:00
-- url     : https://prove2.me/submissions/d4abdc46-dc81-47b9-9013-eac94d8ef267

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InSupportOfIsSubquotient
import Theorems.Thm_GlobalTheory_JacquetExact_isSubquotient_jac
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open GlobalTheory GlobalTheory.JacquetExact
namespace GlobalTheory.JacquetExact
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n k) V)
    (τ : Representation ℂ (GL n k) W) (χ : kˣ →* ℂˣ) (hτ : IsSmooth τ) (h : IsSubquotient π τ)
    (hχ : InSupport π χ) : InSupport τ χ := by
  obtain ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub, hact⟩ := hχ
  exact ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub.trans (isSubquotient_jac e hτ h), hact⟩
end GlobalTheory.JacquetExact
