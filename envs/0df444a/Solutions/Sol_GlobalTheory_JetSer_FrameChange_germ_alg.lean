-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.germ_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:30.332389+00:00
-- url     : https://prove2.me/submissions/244c3e67-fb2d-4833-b891-668219f39dca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution {A : Type} [CommRing A] (f f' : A) (e c r' : Aˣ) (m : ℕ) (σ' : A)
    (h' : f' * r'.val ^ m = σ') (h : f * ((c * e⁻¹) * r').val ^ m = (c ^ m).val * σ') : f' * e.val ^ m = f := by
  rw [← h', ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at h
  rw [← Units.val_pow_eq_pow_val, ← Units.mul_left_inj ((c * e⁻¹ * r') ^ m), h, _root_.mul_assoc, ← Units.val_mul,
    mul_left_comm, ← Units.val_mul]
  congr 2
  rw [← mul_pow, ← mul_pow]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.JetSer.FrameChange
