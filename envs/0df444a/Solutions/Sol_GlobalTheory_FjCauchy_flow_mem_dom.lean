-- Prove2me | solution 1 for GlobalTheory.FjCauchy.flow_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:51:57.063646+00:00
-- url     : https://prove2.me/submissions/9a43624d-9dc5-46e3-9828-3e252f627332

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_det_flowMat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_det_flowMat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_dmin_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hG_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hsg_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_maj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_mN_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory.FjCauchy
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem one_add_two_mul_pos_of_le {c y h hp : ℝ} (hc : 0 < c) (h0 : 0 ≤ h) (hle : h ≤ hp)
    (hpos : 0 < 1 + 2 * c * y * hp) : 0 < 1 + 2 * c * y * h := by
  rcases le_or_gt 0 y with hy | hy
  · have : 0 ≤ 2 * c * y * h := by positivity
    linarith
  · have h1 : 0 ≤ hp - h := sub_nonneg.2 hle
    have h2 : 0 < -y := by linarith
    have : 0 ≤ 2 * c * (-y) * (hp - h) := by positivity
    nlinarith
open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem one_add_two_mul_pos_of_inv_add_pos {c y hp : ℝ} (hc : 0 < c) (hp0 : 0 < hp)
    (hs : 0 < 1 / (c * (2 * hp)) + y) : 0 < 1 + 2 * c * y * hp := by
  have hk : 0 < c * (2 * hp) := by positivity
  have e : (1 / (c * (2 * hp)) + y) * (c * (2 * hp)) = 1 + 2 * c * y * hp := by
    rw [add_mul, one_div, inv_mul_cancel₀ hk.ne']
    ring
  rw [← e]
  exact mul_pos hs hk
end GlobalTheory.FjCauchy
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.FjCauchy
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open NumberField Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
namespace GlobalTheory.FjCauchy
namespace _root_.GlobalTheory.FjCauchy
theorem _root_.solution {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 < X.tt ξ x τ + (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl]
  have hx' := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx' ⊢
  intro τ
  obtain ⟨hdet, hmin⟩ := hx' τ
  constructor
  · show (X.flowMatV (X.embV ξ τ) τ (s τ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0
    rw [Matrix.det_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat X _ τ _ (hiso τ).1, one_mul]
    exact hdet
  · intro i
    have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
    have hmaj := X.maj_pos hx τ (hiso τ).2
    have hsτ := hs τ
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt at hsτ
    change 0 < 1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im at hsτ
    have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) hdet (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ)
      (X.embV ξ τ) (hiso τ).1 i (Nat.lt_succ_iff.mp i.isLt)
    have hmi := hmin i
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq] at hmi ⊢
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, Complex.re_mul_ofReal, ← mul_assoc]
    rw [hm0] at hmaj hsτ
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
    have hp0 : 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 := by linarith
    exact mul_pos hmi (one_add_two_mul_pos_of_le hc hb.1 hb.2 (one_add_two_mul_pos_of_inv_add_pos hc hp0 hsτ))
end _root_.GlobalTheory.FjCauchy
end GlobalTheory.FjCauchy
