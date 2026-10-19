-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.algebraGenerating_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:34:41.337301+00:00
-- url     : https://prove2.me/submissions/77bde93f-2a0a-447f-8baa-8cc9e0d103e2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean:L143-L167
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.algebraGenerating_fourier. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Theorems.Thm_OAI_DirectCrouzeix_Faber_algebraGenerating_coefficient

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

theorem taylorCoeff_eq_series {E : Type u_102} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) : taylorCoeff f k = p.coeff k := by
  have hh := hp.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin k => (1:ℂ))
  simp only [← iteratedDeriv_eq_iteratedFDeriv,Finset.sum_const,Finset.card_univ,
    Fintype.card_perm,Fintype.card_fin] at hh
  change iteratedDeriv k f 0 = k.factorial • p.coeff k at hh
  rw [taylorCoeff,hh,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  simp [Nat.factorial_ne_zero]

theorem unitPoint_continuous : Continuous unitPoint := (fourier 1).continuous

theorem unitPoint_pow (t : Angle) (k : ℕ) : unitPoint t ^ k = fourier (k:ℤ) t := by
  simp only [unitPoint,fourier_apply,one_zsmul,← Circle.coe_pow,
    ← AddCircle.toCircle_nsmul,natCast_zsmul]

theorem integral_character_smul {E : Type u_103} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (a b : ℤ) (v : E) :
    (∫ t : Angle, fourier (-a) t • (fourier b t • v) ∂angularMeasure) = if b = a then v else 0 := by
  rw [show (fun t : Angle => fourier (-a) t • (fourier b t • v)) =
      (fun t => (fourier (-a) t * fourier b t) • v) by funext t; rw [smul_smul],
    integral_smul_const]
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) b) a
  change (∫ t : Angle, fourier (-a) t * fourier b t ∂angularMeasure) = _ at hh
  rw [hh]
  by_cases hab : b = a
  · subst b; simp
  · simp [Ne.symm hab,hab]

theorem fourierCoeff_of_powerSeries {E : Type u_104} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 r) (hr : 1 < r) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  have h1 : (1:ℂ) ∈ Metric.eball 0 p.radius := by
    simpa [Metric.mem_eball,edist_dist] using hr.trans_le hp.r_le
  have hs : Summable (fun n => ‖p.coeff n‖) := by
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,one_pow,one_smul] using p.summable_norm_apply h1
  have hp' (t : Angle) : HasSum (fun n : ℕ => fourier n t • p.coeff n) (f (unitPoint t)) := by
    have ht : unitPoint t ∈ Metric.eball 0 r := by
      simpa [Metric.mem_eball,edist_dist] using hr
    simpa only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,unitPoint_pow,zero_add] using hp.hasSum ht
  have hi := hasSum_integral_of_dominated_convergence
    (μ := angularMeasure) (bound := fun (n : ℕ) (_ : Angle) => ‖p.coeff n‖)
    (F := fun (n : ℕ) (t : Angle) => fourier (-k) t • (fourier n t • p.coeff n))
    (f := fun t => fourier (-k) t • f (unitPoint t))
    (fun n => ((fourier (-k)).continuous.smul ((fourier n).continuous.smul continuous_const)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun t => by simp [norm_smul,fourier_apply,Circle.norm_coe]))
    (ae_of_all _ (fun _ => hs)) (integrable_const _)
    (ae_of_all _ (fun t => (hp' t).const_smul (fourier (-k) t)))
  simp only [integral_character_smul] at hi
  change HasSum (fun n : ℕ => if (n:ℤ) = k then p.coeff n else 0)
    (fourierCoeff (fun t : Angle => f (unitPoint t)) k) at hi
  rw [← hi.tsum_eq]
  cases k with
  | ofNat k =>
    simp [taylorCoeff_eq_series hp]
  | negSucc k =>
    simp

theorem fourierCoeff_of_analytic {E : Type u_105} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f (unitPoint t)) k =
      if 0 ≤ k then taylorCoeff f k.toNat else 0 := by
  obtain ⟨ρ,hρ1,hρR⟩ := exists_between hR
  let ρ' : ℝ≥0 := ⟨ρ,by linarith⟩
  have hd : DifferentiableOn ℂ f (closedBall 0 (ρ':ℝ)) :=
    hf.differentiableOn.mono (closedBall_subset_ball hρR)
  have hp := hd.hasFPowerSeriesOnBall (R := ρ') (by change 0 < ρ; linarith)
  apply fourierCoeff_of_powerSeries hp
  exact_mod_cast hρ1

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

theorem fourierCoeff_comp_neg {E : Type u_106} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Angle → E) (k : ℤ) :
    fourierCoeff (fun t => f (-t)) k = fourierCoeff f (-k) := by
  unfold fourierCoeff
  rw [← integral_neg_eq_self (fun t : Angle => fourier (-k) t • f (-t)) angularMeasure]
  congr 1
  funext t
  simp [fourier_apply,smul_neg,neg_smul]

theorem fourierCoeff_of_antianalytic {E : Type u_107} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} {R : ℝ} (hR : 1 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) (k : ℤ) :
    fourierCoeff (fun t : Angle => f ((unitPoint t)⁻¹)) k =
      if k ≤ 0 then taylorCoeff f (-k).toNat else 0 := by
  have he : (fun t : Angle => f ((unitPoint t)⁻¹)) = (fun t => (fun s => f (unitPoint s)) (-t)) := by
    funext t; change f ((unitPoint t)⁻¹) = f (unitPoint (-t)); rw [unitPoint_neg]
  rw [he,fourierCoeff_comp_neg (fun t : Angle => f (unitPoint t)) k,fourierCoeff_of_analytic hR hf]
  simp only [neg_nonneg]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.BoundaryKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem unitPoint_ne_zero (t : Angle) : unitPoint t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [unitPoint_norm]; norm_num)

theorem unitPoint_inv_mem {R : ℝ} (hR : 1 < R) (t : Angle) :
    (unitPoint t)⁻¹ ∈ ball (0:ℂ) R := by
  simpa only [mem_ball,dist_zero_right,norm_inv,unitPoint_norm,inv_one] using hR

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_129 u_130

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section BanachAlgebra

variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem analyticAt_ringInverse {x : 𝔄} (hx : IsUnit x) :
    AnalyticAt ℂ Ring.inverse x := by
  rcases hx with ⟨u,rfl⟩
  exact analyticAt_inverse u

theorem analyticAt_algebraDenominator {𝔄 : Type u_129} [NormedRing 𝔄]
    [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) : AnalyticAt ℂ (algebraDenominator c g A) u := by
  exact ((analyticAt_const.add (analyticAt_id.mul hg)).smul analyticAt_const).sub
    (analyticAt_id.smul analyticAt_const)

theorem analyticAt_algebraGenerating {c : ℂ} {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g u) (A : 𝔄) (hu : IsUnit (algebraDenominator c g A u)) :
    AnalyticAt ℂ (algebraGenerating c g A) u :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).smul
    ((analyticAt_ringInverse hu).comp (analyticAt_algebraDenominator hg A))

theorem algebraGenerating_fourier {R : ℝ} (hR : 1 < R) {c : ℂ} (hc : c ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball 0 R)) (A : 𝔄)
    (hunit : ∀ u ∈ closedBall 0 1, IsUnit (algebraDenominator c g A u)) :
    (Continuous (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)) ∧
    (∀ k : ℕ, fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)
      (-(k:ℤ)) = Polynomial.aeval A (faberBasis c g k)) ∧
    (∀ k : ℤ, 0 < k → fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹) k = 0) := by
  have ha : AnalyticOnNhd ℂ (algebraGenerating c g A) (closedBall 0 1) := by
    intro u hu
    exact analyticAt_algebraGenerating (hg u (closedBall_subset_ball hR hu)) A (hunit u hu)
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall (0:ℂ) 1).exists_thickening_subset_open
    (isOpen_analyticAt ℂ (algebraGenerating c g A)) ha
  rw [thickening_closedBall hδ (by norm_num : (0:ℝ) ≤ 1)] at hsub
  have hδ1 : 1 < δ+1 := by linarith
  have hsub : AnalyticOnNhd ℂ (algebraGenerating c g A) (ball 0 (δ+1)) := hsub
  have he (k : ℤ) := fourierCoeff_of_antianalytic hδ1 hsub k
  refine ⟨?_,?_,?_⟩
  · exact hsub.continuousOn.comp_continuous (unitPoint_continuous.inv₀ unitPoint_ne_zero)
      (fun t => unitPoint_inv_mem hδ1 t)
  · intro k
    rw [he,ite_eq_left (by omega : -(k:ℤ) ≤ 0)]
    simp only [neg_neg,Int.toNat_natCast]
    exact algebraGenerating_coefficient hc (hg 0 (mem_ball_self (by linarith))) A k
  · intro k hk
    rw [he,ite_eq_right (by omega : ¬k ≤ 0)]

end BanachAlgebra

end DirectCrouzeix.Faber

namespace DirectCrouzeix

open MeasureTheory Set Filter Metric

open scoped Topology ComplexConjugate MatrixOrder ComplexOrder

end DirectCrouzeix

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.algebraGenerating_fourier := @_root_.OAI.DirectCrouzeix.Faber.algebraGenerating_fourier
