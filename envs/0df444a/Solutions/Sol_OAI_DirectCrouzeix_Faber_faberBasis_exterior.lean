-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.faberBasis_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:18:14.082882+00:00
-- url     : https://prove2.me/submissions/31122b8a-2006-4511-a61d-15018ac7f33e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean:L162-L181
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.faberBasis_exterior. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Theorems.Thm_OAI_DirectCrouzeix_Faber_correction_identity
import Theorems.Thm_OAI_DirectCrouzeix_Faber_hasDerivAt_chordIntegral_left
import Theorems.Thm_OAI_DirectCrouzeix_Faber_scalarGenerating_coefficient

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem analyticOnNhd_chordIntegral_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f s) {w : Parameter → ℂ} (hw : Continuous w)
    {v : ℂ} (hv : v ∈ s) : AnalyticOnNhd ℂ (fun u => chordIntegral f w u v) s := by
  apply DifferentiableOn.analyticOnNhd _ hs
  intro u hu
  exact (hasDerivAt_chordIntegral_left hs hconv hf hw hu hv).differentiableAt.differentiableWithinAt

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.DividedDifferences ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem analyticOnNhd_correction_left {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) {c v : ℂ} (hv : v ∈ s)
    (hH : ∀ u ∈ s, chordDenominator c g u v ≠ 0) :
    AnalyticOnNhd ℂ (fun u => correction c g u v) s := by
  have hD := analyticOnNhd_chordIntegral_left hs hconv hg.deriv (continuous_const (y := (1:ℂ))) hv
  have hE := analyticOnNhd_chordIntegral_left hs hconv hg.deriv.deriv
    (show Continuous (fun t : Parameter => ((1-(t:ℝ) : ℝ):ℂ)) by fun_prop) hv
  intro u hu
  exact (((analyticAt_id.mul analyticAt_const).mul ((hD u hu).add (analyticAt_id.mul (hE u hu)))).div
    (analyticAt_const.sub ((analyticAt_id.mul analyticAt_const).mul (hD u hu))) (hH u hu))

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem taylorCoeff_congr {E : Type u_96} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : taylorCoeff f k = taylorCoeff g k := by
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq k]

theorem taylorCoeff_add {E : Type u_97} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    taylorCoeff (fun z => f z+g z) k = taylorCoeff f k+taylorCoeff g k := by
  simp only [taylorCoeff,iteratedDeriv_fun_add (n := k) hf.contDiffAt hg.contDiffAt,smul_add]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberPolynomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem faberBasis_eval (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (faberBasis c g k).eval z = ∑ j ∈ Finset.range (k+1),
      taylorCoeff (fun u => localN c g u * localW c g u^j) k * z^j := by
  simp [faberBasis,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem analyticAt_scalarGenerating {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) : AnalyticAt ℂ (scalarGenerating c g z) 0 := by
  apply (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).div
    (analyticAt_const.add (analyticAt_id.mul (hg.sub analyticAt_const)))
  simpa using hc

theorem taylorCoeff_geometric (z : ℂ) (k : ℕ) :
    taylorCoeff (fun u : ℂ => (1-z*u)⁻¹) k = z^k := by
  have he : (fun u : ℂ => (1-z*u)⁻¹) = scalarGenerating 1 (fun _ => 0) z := by
    funext u
    simp [scalarGenerating,sub_eq_add_neg,mul_comm]
  rw [he,scalarGenerating_coefficient (by norm_num) analyticAt_const,faberBasis_eval]
  have he' (j : ℕ) : (fun u => localN 1 (fun _ => 0) u * localW 1 (fun _ => 0) u^j) =
      (fun u : ℂ => u^j) := by funext u; simp [localN,localW,localL]
  simp_rw [he']
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  simp only [taylorCoeff,iteratedDeriv_fun_pow_zero,smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp [hfac]
  · intro j hj hjk
    simp [Ne.symm hjk]
  · simp

theorem faberBasis_exterior {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    {v : ℂ} (hv : v ∈ ball 0 R) (hv0 : v ≠ 0)
    (hH : ∀ u ∈ ball 0 R, chordDenominator c g u v ≠ 0) (k : ℕ) :
    (faberBasis c g k).eval (exterior c g v⁻¹) = v⁻¹^k +
      taylorCoeff (fun u => correction c g u v) k := by
  have h0 : (0:ℂ) ∈ ball 0 R := mem_ball_self hR
  have hgen := analyticAt_scalarGenerating hc (hg 0 h0) (exterior c g v⁻¹)
  have hcorr := analyticOnNhd_correction_left isOpen_ball (convex_ball 0 R) hg hv hH
  have hgeom : AnalyticAt ℂ (fun u : ℂ => (1-v⁻¹*u)⁻¹) 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).inv (by simp)
  have he : scalarGenerating c g (exterior c g v⁻¹) =ᶠ[𝓝 0]
      (fun u => (1-v⁻¹*u)⁻¹+correction c g u v) := by
    filter_upwards [isOpen_ball.mem_nhds h0, (isOpen_ne.mem_nhds (Ne.symm hv0))] with u hu huv
    have hh := correction_identity isOpen_ball (convex_ball 0 R) hg c hu hv hv0 huv (hH u hu)
    change correction c g u v = scalarGenerating c g (exterior c g v⁻¹) u - _ at hh
    rw [div_eq_mul_inv,mul_comm] at hh
    linear_combination -hh
  rw [← scalarGenerating_coefficient hc (hg 0 h0),taylorCoeff_congr he,
    taylorCoeff_add hgeom (hcorr 0 h0),taylorCoeff_geometric]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.faberBasis_exterior := @_root_.OAI.DirectCrouzeix.Faber.faberBasis_exterior
