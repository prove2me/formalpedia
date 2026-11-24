-- Prove2me | solution 1 for GlobalTheory.Unfold.unique_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:10.096364+00:00
-- url     : https://prove2.me/submissions/27895ed5-6249-4a16-bea4-90ef21f4bb66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_invF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_assoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_invF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_rmul_oneF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_lact_rmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Unfold
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Unfold
theorem _root_.solution (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by
  obtain ⟨z, hz, b, hb, h⟩ := h
  obtain ⟨z', hz', b', hb', h'⟩ := h'
  have hδ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ
  have e1 : lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) b) = rmul (cpt X x0 z') b' := by
    rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hbb := ExtFPf.mul_mem X hb (ExtFPf.invF_mem X hb')
  have e2 : cpt X x0 z' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) (rmul b (ExtFPf.invF X b'))) := by
    rw [← ExtFPf.rmul_assoc, FundSetPf.lact_rmul, e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb',
      ExtFPf.rmul_oneF]
  obtain rfl : z = z' := hF.2.2.1 z hz z' hz' _ hδ _ hbb e2
  have e3 : lact (γ'⁻¹ * γ) (cpt X x0 z) = rmul (cpt X x0 z) (rmul b' (ExtFPf.invF X b)) := by
    rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
      ExtFPf.rmul_oneF]
  have := X.Γ_free _ hδ _ (hF.2.1 hz) _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e3
  exact (inv_mul_eq_one.mp this).symm
end GlobalTheory.Unfold
