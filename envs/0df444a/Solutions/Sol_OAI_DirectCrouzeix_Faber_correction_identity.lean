-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.correction_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:13:09.621358+00:00
-- url     : https://prove2.me/submissions/7af307a1-adcd-4823-a726-1d382403edaa

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean:L140-L156
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.correction_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Theorems.Thm_OAI_DirectCrouzeix_Faber_chordIntegral_deriv_mul
import Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_chordIntegral_left

-- ---- from OAI.Analysis.DirectCrouzeix.DividedDifferences ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem hasDerivAt_divided_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    HasDerivAt (fun z => divided g z v) (dividedLeft g u v) u := by
  simpa only [divided, dividedLeft, one_mul] using
    hasDerivAt_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hu hv

theorem divided_fundamental {s : Set ℂ} (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    (u-v)*divided g u v = g u-g v := by
  have hh := chordIntegral_deriv_mul hconv hg hu hv
  change divided g u v * (v-u) = _ at hh
  linear_combination -hh

theorem divided_derivative_relation {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {u v : ℂ} (hu : u ∈ s) (hv : v ∈ s) :
    divided g u v + (u-v)*dividedLeft g u v = deriv g u := by
  have hd := ((hasDerivAt_id u).sub_const v).mul (hasDerivAt_divided_left hs hconv hg hu hv)
  have he : (fun z => g z-g v) =ᶠ[𝓝 u] (fun z => (z-v)*divided g z v) := by
    filter_upwards [hs.mem_nhds hu] with z hz
    exact (divided_fundamental hconv hg hz hv).symm
  have hid := (hd.congr_of_eventuallyEq he).unique ((hg u hu).differentiableAt.hasDerivAt.sub_const (g v))
  simpa using hid

theorem correction_identity {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hH : chordDenominator c g u v ≠ 0) :
    correction c g u v = (c-u^2*deriv g u)/(c+u*(g u-exterior c g v⁻¹)) - (1-u/v)⁻¹ := by
  have hD := divided_fundamental hconv hg hu hv
  have hE := divided_derivative_relation hs hconv hg hu hv
  have huv' : v-u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have he : c+u*(g u-exterior c g v⁻¹) = chordDenominator c g u v * (v-u)/v := by
    simp only [exterior,inv_inv,chordDenominator]
    field_simp
    linear_combination -u*v*hD
  rw [he,correction]
  have hd0 : chordDenominator c g u v * (v-u) / v ≠ 0 := div_ne_zero (mul_ne_zero hH huv') hv0
  field_simp
  simp only [chordDenominator]
  linear_combination -u^2*hE

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.correction_identity := @_root_.OAI.DirectCrouzeix.Faber.correction_identity
