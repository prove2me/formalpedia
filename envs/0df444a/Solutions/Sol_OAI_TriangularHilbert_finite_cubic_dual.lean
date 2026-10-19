-- Prove2me | solution 1 for OAI.TriangularHilbert.finite_cubic_dual
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:04:31.374517+00:00
-- url     : https://prove2.me/submissions/dd64d92d-9fa4-4100-bc7b-e0feb7cc6df0

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

open OAI OAI.TriangularHilbert
universe uι
open scoped BigOperators
lemma h43_cd_pt (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ((t:ℂ) * (starRingEnd ℂ) z / (Real.sqrt ‖z‖ : ℂ)) * z = ((t * (‖z‖ * Real.sqrt ‖z‖) : ℝ) : ℂ) ∧
    ‖(t:ℂ) * (starRingEnd ℂ) z / (Real.sqrt ‖z‖ : ℂ)‖^3 = t^3 * (‖z‖ * Real.sqrt ‖z‖) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set s := Real.sqrt ‖z‖ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hn
  have hss : s * s = ‖z‖ := Real.mul_self_sqrt hn.le
  constructor
  · rw [mul_div_assoc, mul_assoc, div_mul_eq_mul_div, Complex.conj_mul']
    have hsc : (s:ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [← hss]; push_cast
    field_simp
  · rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ht, abs_of_pos hs0, ← hss]
    field_simp

theorem solution {ι : Type uι} [Fintype ι] (u : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {K b : ℝ} (hK : 0 < K)
    (H : ∀ f : ι → ℂ, ‖∑ i, (w i:ℂ)*f i*u i‖ ≤ K*((∑ i, w i*‖f i‖^3)+b)) :
    (∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖)) ≤ 4*K*(K+1)*b := by
  set t : ℝ := 1 / (K+1) with htdef
  have ht0 : 0 < t := by positivity
  have hb : 0 ≤ b := by
    have := H (fun _ => 0)
    simp at this
    nlinarith
  set X := ∑ i, w i*(‖u i‖*Real.sqrt ‖u i‖) with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by positivity))
  have hH := H (fun i => (t:ℂ) * (starRingEnd ℂ) (u i) / (Real.sqrt ‖u i‖ : ℂ))
  have e1 : (∑ i, (w i:ℂ) * ((t:ℂ) * (starRingEnd ℂ) (u i) / (Real.sqrt ‖u i‖ : ℂ)) * u i) = ((t * X : ℝ) : ℂ) := by
    rw [hX, Finset.mul_sum]; push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_assoc, (h43_cd_pt (u i) t ht0.le).1]; push_cast; ring
  have e2 : (∑ i, w i * ‖(t:ℂ) * (starRingEnd ℂ) (u i) / (Real.sqrt ‖u i‖ : ℂ)‖^3) = t^3 * X := by
    rw [hX, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(h43_cd_pt (u i) t ht0.le).2]; ring
  rw [e1, e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hH
  -- hH : t * X ≤ K * (t^3 * X + b)
  have hK1 : 0 < K + 1 := by linarith
  have htK : t * (K+1) = 1 := by rw [htdef]; field_simp
  have h1 : X * (K+1)^2 ≤ K * X + K * b * (K+1)^3 := by
    have := mul_le_mul_of_nonneg_left hH (by positivity : (0:ℝ) ≤ (K+1)^3)
    have e : (K+1)^3 * (t * X) = X * (K+1)^2 * (t*(K+1)) := by ring
    have e' : (K+1)^3 * (K * (t^3 * X + b)) = K * X * (t*(K+1))^3 + K * b * (K+1)^3 := by ring
    rw [e, e', htK] at this
    simpa using this
  have h2 : 3/4 * (K+1)^2 * X ≤ X * (K+1)^2 - K * X := by nlinarith [sq_nonneg (K-1)]
  have h3 : 3/4 * (K+1)^2 * X ≤ K * b * (K+1)^3 := by linarith
  have h4 : X ≤ 4/3 * K * b * (K+1) := by
    have hpos : 0 < (K+1)^2 := by positivity
    have : (K+1)^2 * X ≤ (K+1)^2 * (4/3 * K * b * (K+1)) := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  nlinarith [mul_nonneg (mul_nonneg hK.le hb) hK1.le]

