-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames.zDet_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:34.518631+00:00
-- url     : https://prove2.me/submissions/8b7707db-5104-45e0-b6a1-d6af9aa9436f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped Matrix ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
theorem _root_.solution {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) : 0 < zDet X z τ := by
  set Z := zBlock X z τ with hZ
  have hn : zNorm X z τ < 1 := hz τ
  have hquad : ∀ x, star x ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ x) = star x ⬝ᵥ x - star (Z *ᵥ x) ⬝ᵥ (Z *ᵥ x) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
      Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hsq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ), star v ⬝ᵥ v = ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : ℂ) := by
    intro ι _ v
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
    rw [Complex.ofReal_pow]
    exact h
  have hpd : (1 - Zᴴ * Z).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
    · intro x hx
      rw [hquad, hsq, hsq, ← Complex.ofReal_sub, Complex.zero_lt_real, sub_pos]
      have hx0 : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
      have hle : ‖WithLp.toLp 2 (Z *ᵥ x)‖ ≤ zNorm X z τ * ‖WithLp.toLp 2 x‖ :=
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm (WithLp.toLp 2 x)
      have hlt : ‖WithLp.toLp 2 (Z *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ :=
        lt_of_le_of_lt hle (by nlinarith [norm_nonneg (WithLp.toLp 2 (Z *ᵥ x))])
      exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  have hdet := hpd.det_pos
  exact (Complex.lt_def.mp hdet).1
end GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
