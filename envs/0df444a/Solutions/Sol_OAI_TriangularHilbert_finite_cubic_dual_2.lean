-- Prove2me | solution 2 for OAI.TriangularHilbert.finite_cubic_dual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:20:43.296096+00:00
-- url     : https://prove2.me/submissions/135f5679-416b-4938-a3eb-93b89220b5e3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/FiniteDual.lean:L35-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.finite_cubic_dual. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual

-- ---- from OAI.Analysis.TriangularHilbert.FiniteDual ----
namespace OAI

universe uι

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma dualRoot_mul (z : ℂ) : dualRoot z*z = (‖z‖*Real.sqrt ‖z‖:ℝ) := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  unfold dualRoot
  rw [div_mul_eq_mul_div, mul_assoc, RCLike.star_def,Complex.conj_mul']
  push_cast
  field_simp

lemma norm_dualRoot (z : ℂ) : ‖dualRoot z‖ = Real.sqrt ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp [dualRoot]
  unfold dualRoot
  rw [norm_div,norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)]

lemma cube_norm_dualRoot (z : ℂ) : ‖dualRoot z‖^3 = ‖z‖*Real.sqrt ‖z‖ := by
  rw [norm_dualRoot,pow_succ,Real.sq_sqrt (norm_nonneg _)]

lemma finite_cubic_dual {ι : Type uι} [Fintype ι] (u : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {K b : ℝ} (hK : 0 < K)
    (H : ∀ f : ι → ℂ, ‖∑ i, (w i:ℂ)*f i*u i‖ ≤ K*((∑ i, w i*‖f i‖^3)+b)) :
    (∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)) ≤ 4*K*(K+1)*b := by
  let d : ℝ := 1/(2*(K+1))
  let m : ℝ := ∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 0 ≤ m := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by positivity))
  have hd1 : d ≤ 1 := by
    dsimp [d]
    rw [div_le_one (by positivity)]
    linarith
  have hk1 : K*d ≤ 1/2 := by
    dsimp [d]
    rw [← mul_div_assoc, mul_one,div_le_iff₀ (by positivity)]
    linarith
  have hk2 : K*d^3 ≤ d/2 := by
    have ha := mul_le_mul_of_nonneg_right hk1 (sq_nonneg d)
    nlinarith [mul_le_mul_of_nonneg_left hd1 hd.le]
  let f : ι → ℂ := fun i => (d:ℂ)*dualRoot (u i)
  have hprod (i : ι) : (w i:ℂ)*f i*u i = (d*(w i*(‖u i‖*Real.sqrt ‖u i‖)):ℝ) := by
    dsimp [f]
    rw [mul_assoc,mul_assoc,dualRoot_mul]
    push_cast
    ring
  have hnorm (i : ι) : w i*‖f i‖^3 = d^3*(w i*(‖u i‖*Real.sqrt ‖u i‖)) := by
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hd.le,mul_pow,cube_norm_dualRoot]
    ring
  have hp : (∑ i, (w i:ℂ)*f i*u i) = (d*m:ℝ) := by
    simp_rw [hprod]
    rw [← Complex.ofReal_sum,← Finset.mul_sum]
  have ha := H f
  rw [hp,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hd.le hm)] at ha
  simp_rw [hnorm] at ha
  rw [← Finset.mul_sum] at ha
  change d*m ≤ K*(d^3*m+b) at ha
  have hb : m ≤ (2*K/d)*b := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_right hk2 hm]
  apply hb.trans_eq
  dsimp [d]
  field_simp
  ring
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.finite_cubic_dual.{uι} := @_root_.OAI.TriangularHilbert.finite_cubic_dual.{uι}
