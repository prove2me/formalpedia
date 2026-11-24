-- Prove2me | solution 1 for GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:53:24.612698+00:00
-- url     : https://prove2.me/submissions/8fff01e9-f953-4b3f-954a-132fefd3da26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.MajorantOrthFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantOrthFrame
namespace _root_.GlobalTheory.MajorantOrthFrame
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
      (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
        X.maj x τ v = ∑ a, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by
  intro r X x hx
  refine ⟨_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx, fun τ v => ?_⟩
  have hdet : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 := _root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx τ
  have hG : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := hx τ
  set P := _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ with hP
  set c := P⁻¹ *ᵥ v with hc
  have hv : v = P *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v (_root_.ReciprocityTheory.ChartRestriction.G.FD.col P a) = c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := by
    intro a
    have hcolumn : _root_.ReciprocityTheory.ChartRestriction.G.FD.col P a = P *ᵥ Pi.single a 1 := by
      ext i
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec_single_one]
    rw [hcolumn, hv, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]
  have hvv : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v v = ∑ a, c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) * star (c a) := by
    conv_lhs => rw [hv]
    rw [_root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, mul_assoc]
  have hgp : X.gramPos x τ = 1 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos
    rw [← hP, hG]
    ext a b
    simp [Matrix.one_apply, Matrix.diagonal_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have hp : X.p0 ≤ r := X.p0_le
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.posPart
  rw [hgp, hvv]
  simp only [← hP, inv_one, Matrix.one_apply, hcol]
  simp [Finset.sum_ite_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have key : ∀ f : Fin r → ℝ,
      ∑ b : Fin X.p0, f (Fin.castLE hp b) = ∑ a : Fin r, if (a : ℕ) < X.p0 then f a else 0 := by
    intro f
    have hmap := Finset.sum_map Finset.univ (Fin.castLEEmb hp) f
    simp only [Fin.castLEEmb_apply] at hmap
    rw [← Finset.sum_filter, ← hmap]
    congr 1
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.isLt
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
  rw [key fun a => (c a).re * (c a).re + (c a).im * (c a).im, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  split_ifs <;> ring
end _root_.GlobalTheory.MajorantOrthFrame
end GlobalTheory.MajorantOrthFrame
