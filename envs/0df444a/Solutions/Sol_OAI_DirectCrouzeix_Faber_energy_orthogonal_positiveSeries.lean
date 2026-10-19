-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:29:11.486666+00:00
-- url     : https://prove2.me/submissions/04541e92-05b7-448e-a971-fa2dc7c0a41e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean:L162-L186
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries. The node keeps its source
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
import Theorems.Thm_OAI_DirectCrouzeix_Faber_integral_inner_positiveSeries

-- ---- from OAI.Analysis.DirectCrouzeix.CompactIntegrals ----
namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem integrable_of_continuous_compact {α : Type u_87} {E : Type u_88} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [CompactSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.KernelContraction ----
namespace OAI

universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

section Hilbert

variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem continuous_positiveSeries {E : Type u_127} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {N : ℕ} (C : Fin N → E) :
    Continuous (positiveSeries C) := by
  exact continuous_finsetSum _ (fun k _ => (fourier (k:ℤ)).continuous.smul continuous_const)

theorem fourierCoeff_finite_smul {N : ℕ} (f : Fin N → Angle → ℂ)
    (hf : ∀ k, Continuous (f k)) (C : Fin N → E) (j : ℤ) :
    fourierCoeff (fun t => ∑ k, f k t • C k) j = ∑ k, fourierCoeff (f k) j • C k := by
  unfold fourierCoeff
  simp_rw [Finset.smul_sum,smul_smul]
  rw [integral_finsetSum]
  · simp_rw [integral_smul_const,smul_eq_mul]
  · intro k hk
    exact integrable_of_continuous_compact _ (((fourier (-j)).continuous.mul (hf k)).smul continuous_const)

theorem fourierCoeff_positiveSeries {N : ℕ} (C : Fin N → E) (j : Fin N) :
    fourierCoeff (positiveSeries C) (j:ℤ) = C j := by
  classical
  unfold positiveSeries
  rw [fourierCoeff_finite_smul _ (fun k => (fourier (k:ℤ)).continuous)]
  simp_rw [fourierCoeff_fourier]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
  have hinj (k : Fin N) : (j:ℤ) = (k:ℤ) ↔ j = k := by
    constructor
    · intro h; apply Fin.ext; exact_mod_cast h
    · intro h; rw [h]
  simp_rw [hinj]
  simp

theorem energy_positiveSeries {N : ℕ} (C : Fin N → E) :
    (∫ t, ‖positiveSeries C t‖^2 ∂angularMeasure) = ∑ k, ‖C k‖^2 := by
  have hp := continuous_positiveSeries C
  have he (t : Angle) : ‖positiveSeries C t‖^2 = RCLike.re (inner ℂ (positiveSeries C t) (positiveSeries C t)) := by
    simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]
  simp_rw [he]
  rw [integral_re (integrable_of_continuous_compact _ (hp.inner hp)),integral_inner_positiveSeries C _ hp]
  simp only [fourierCoeff_positiveSeries,inner_self_eq_norm_sq_to_K,map_sum]
  change (∑ k, ((‖C k‖ : ℂ)^2).re) = ∑ k, ‖C k‖^2
  simp [← Complex.ofReal_pow]

theorem energy_orthogonal_positiveSeries {N : ℕ} (C : Fin N → E)
    (r : Angle → E) (hr : Continuous r) (hfreq : ∀ j : ℤ, 0 ≤ j → fourierCoeff r j = 0) :
    (∫ t, ‖positiveSeries C t+r t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖r t‖^2 ∂angularMeasure := by
  have hp := continuous_positiveSeries C
  have hci : Integrable (fun t => inner ℂ (positiveSeries C t) (r t)) angularMeasure :=
    integrable_of_continuous_compact _ (hp.inner hr)
  have hcross : (∫ t, inner ℂ (positiveSeries C t) (r t) ∂angularMeasure) = 0 := by
    rw [integral_inner_positiveSeries C r hr]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hfreq (k:ℤ) (by positivity),inner_zero_right]
  have hcrossRe : (∫ t, RCLike.re (inner ℂ (positiveSeries C t) (r t)) ∂angularMeasure) = 0 := by
    rw [integral_re hci,hcross]
    rfl
  have hpi : Integrable (fun t => ‖positiveSeries C t‖^2) angularMeasure :=
    integrable_of_continuous_compact _ (hp.norm.pow 2)
  have hri : Integrable (fun t => ‖r t‖^2) angularMeasure := integrable_of_continuous_compact _ (hr.norm.pow 2)
  have hcii : Integrable (fun t => 2*RCLike.re (inner ℂ (positiveSeries C t) (r t))) angularMeasure :=
    hci.re.const_mul 2
  simp_rw [norm_add_sq (𝕜 := ℂ)]
  have ha := integral_add (hpi.add hcii) hri
  have hb := integral_add hpi hcii
  simp only [Pi.add_apply] at ha hb
  rw [ha,hb,integral_const_mul,hcrossRe,mul_zero,add_zero,energy_positiveSeries]

end Hilbert

section FaberHilbert

variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FaberHilbert

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries := @_root_.OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries
