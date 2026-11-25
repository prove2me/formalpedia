-- Prove2me | solution 1 for GlobalTheory.NormFactor.pnormInv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:39.056962+00:00
-- url     : https://prove2.me/submissions/ebd151bc-ba07-4e7d-8d15-b0513b3f3f74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormBcharMulNfacRmul
import Theorems.Thm_GlobalTheory_NormFactor_norm_bchar_mul_nfac_rmul
import Theorems.Thm_GlobalTheory_NormFactor_nfacLact_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_chi_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoS_dom_rmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.NormFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl
end GlobalTheory.NormFactor
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.NormFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.NormFactor
namespace _root_.GlobalTheory.NormFactor
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [nfac_eq_prod_norm_dmin_ratio_rpow]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP
  obtain ⟨-, hPb, hPγ⟩ := hP
  have hxb := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  have hlact := _root_.GlobalTheory.NormFactor.nfacLact_holds (E := E)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hlact
  rw [hpn, hpn, hPγ γ hγ _ hxb, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hlact r X la γ hγ _ hxb,
    hPb x hx b hb, norm_mul, ← _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb]
  ring
end _root_.GlobalTheory.NormFactor
end GlobalTheory.NormFactor
