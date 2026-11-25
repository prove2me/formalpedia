-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.summable_prod_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:02.949736+00:00
-- url     : https://prove2.me/submissions/9831ac0e-d303-4ffc-91bd-05aabf692155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a) (N : ℕ) :
    Summable fun x : Fin N → α => ∏ i, g (x i) := by
  induction N with
  | zero => exact .of_finite
  | succ N ih =>
    have h := hg.mul_of_nonneg ih h0 fun x => Finset.prod_nonneg fun i _ => h0 _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => α).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]
end GlobalTheory.SW.EisConv
