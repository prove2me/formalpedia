-- Prove2me | solution 1 for GlobalTheory.FjCauchy.tt_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:53:27.075427+00:00
-- url     : https://prove2.me/submissions/5c3de47e-4486-44e4-91c7-e54c465fb437

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FjCauchyBound
import Theorems.Thm_GlobalTheory_FjCauchy_isIsoV_embV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hsg_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_flow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.FjCauchy
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.FjCauchy
namespace _root_.GlobalTheory.FjCauchy
theorem _root_.solution {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) :
    X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl] at hs ⊢
  have hf : 1 + 2 * X.c τ * (s τ).im *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 ≠ 0 := by
    intro h0
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hs τ X.p0 X.p0_le
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, h0] at h1
    simp at h1
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow X hx (X.embV ξ) τ (hiso τ).1 s hf
  have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
  have hmaj := X.maj_pos hx τ (hiso τ).2
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  change 1 / (X.c τ * X.maj (X.flowV (X.embV ξ) s x) τ (X.embV ξ τ)) =
    1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im
  rw [hm, hm0]
  rw [hm0] at hmaj
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 = H at hf hmaj ⊢
  have hH : H ≠ 0 := by linarith
  have hc' : X.c τ ≠ 0 := hc.ne'
  field_simp
end _root_.GlobalTheory.FjCauchy
end GlobalTheory.FjCauchy
